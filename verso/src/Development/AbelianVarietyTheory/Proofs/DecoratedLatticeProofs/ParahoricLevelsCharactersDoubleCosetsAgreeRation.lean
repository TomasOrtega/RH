import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjSymmEntry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemStabLIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToLocEqMapToMatrix
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainSupportOneOfPattern

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
open GlobalTheory.SymBridge (toLoc IsOrd yPos xPos IsCompl)
open GlobalTheory.SymSupport (InR mem_R_of_inR)

noncomputable section
namespace GlobalTheory.TwBridge.Lev

section Plain
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

/- English proof (translation)
Use `⟨fun l s => ?_, fun r i hl => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero ?_` and prove the remaining obligations. Introduce and unpack `(m | m) -`. Rewrite using `[hg.1, zero_mul]`.

Rewrite using `[hh.1, mul_zero]`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i)]`. Rewrite using `[hh.2 _ i le_rfl, Matrix.one_apply_eq, mul_one, hg.2 r i hl]`. Introduce and unpack `(m | m) - hm`. Break down `r with r | r` into its components or cases.

Rewrite using `[hh.2 (.inl m) i hl, Matrix.one_apply_ne hm, mul_zero]`. Rewrite using `[hg.1, zero_mul]`. Distinguish the cases in `hmi : i.val ≤ m.val`. Rewrite using `[hh.2 (.inr m) i (by simpa [RootEx.lev] using hmi), Matrix.one_apply_ne hm, mul_zero]`. Establish `h1 : RootEx.lev 1 (Sum.inr m : n ⊕ Fin c) < RootEx.lev 1 r` using `lt_of_lt_of_le (by simp only [RootEx.lev, Sum.elim_inr]; omega) hl`.

Rewrite using `[hg.2 r m h1.le, Matrix.one_apply_ne (by rintro rfl; exact lt_irrefl _ h1), zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem inR_mul {g h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (hg : InR g) (hh : InR h) : InR (g * h) := by
  refine ⟨fun l s => ?_, fun r i hl => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero ?_
    rintro (m | m) -
    · rw [hg.1, zero_mul]
    · rw [hh.1, mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i)]
    · rw [hh.2 _ i le_rfl, Matrix.one_apply_eq, mul_one, hg.2 r i hl]
    · rintro (m | m) - hm
      · rcases r with r | r
        · rw [hh.2 (.inl m) i hl, Matrix.one_apply_ne hm, mul_zero]
        · rw [hg.1, zero_mul]
      · by_cases hmi : i.val ≤ m.val
        · rw [hh.2 (.inr m) i (by simpa [RootEx.lev] using hmi), Matrix.one_apply_ne hm, mul_zero]
        · have h1 : RootEx.lev 1 (Sum.inr m : n ⊕ Fin c) < RootEx.lev 1 r := lt_of_lt_of_le (by simp only [RootEx.lev, Sum.elim_inr]; omega) hl
          rw [hg.2 r m h1.le, Matrix.one_apply_ne (by rintro rfl; exact lt_irrefl _ h1), zero_mul]
    · simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `InR (fromBlocks γ.val 0 0 1)`. Use `⟨fun l s => rfl, ?_⟩` and prove the remaining obligations. Introduce and unpack `(r | r) i -`. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply]`.
-/
theorem inR_embX (γ : GL n k) : InR (embX c γ).val := by
  change InR (fromBlocks γ.val 0 0 1)
  refine ⟨fun l s => rfl, ?_⟩
  rintro (r | r) i -
  · simp
  · simp [Matrix.one_apply]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun l s => by rw [h _ _ (by simp [RootEx.lev])]; simp, fun r i hl => h _ _ hl⟩`.
-/
theorem inR_of_inN {g : GL (n ⊕ Fin c) k} (h : InN 1 g) : InR g.val :=
  ⟨fun l s => by rw [h _ _ (by simp [RootEx.lev])]; simp, fun r i hl => h _ _ hl⟩

/- English proof (translation)
Set `S : Subgroup (GL (n ⊕ Fin c) k)` to `{ carrier := {g | InR g.val ∧ InR (g⁻¹).val} one_mem' := by`. Establish `: InR (1 : GL (n ⊕ Fin c) k).val` using `by simpa using inR_embX (c := c) (1 : GL n k)`. Conclude with `⟨this, by rwa [inv_one]⟩`. Use the proof step `mul_mem' := fun {a b} ha hb => ⟨inR_mul ha.1 hb.1, by rw [_root_.mul_inv_rev]; exact inR_mul hb.2 ha.2⟩`. Use the proof step `inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩ }`.

Establish `: GlobalTheory.RootEx.R k n c 1 ≤ S`. Use `sup_le ?_ fun u hu => ⟨inR_of_inN (Model.mem_N_iff.1 hu), inR_of_inN (Model.mem_N_iff.1 (inv_mem hu))⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨γ, rfl⟩`. Conclude with `⟨inR_embX γ, by rw [← map_inv]; exact inR_embX _⟩`. Conclude with `(this h).1`.
-/
theorem inR_of_mem_R {g : GL (n ⊕ Fin c) k} (h : g ∈ GlobalTheory.RootEx.R k n c 1) : InR g.val := by
  let S : Subgroup (GL (n ⊕ Fin c) k) :=
    { carrier := {g | InR g.val ∧ InR (g⁻¹).val}
      one_mem' := by
        have : InR (1 : GL (n ⊕ Fin c) k).val := by simpa using inR_embX (c := c) (1 : GL n k)
        exact ⟨this, by rwa [inv_one]⟩
      mul_mem' := fun {a b} ha hb => ⟨inR_mul ha.1 hb.1, by rw [_root_.mul_inv_rev]; exact inR_mul hb.2 ha.2⟩
      inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩ }
  have : GlobalTheory.RootEx.R k n c 1 ≤ S := by
    refine sup_le ?_ fun u hu => ⟨inR_of_inN (Model.mem_N_iff.1 hu), inR_of_inN (Model.mem_N_iff.1 (inv_mem hu))⟩
    rintro _ ⟨γ, rfl⟩
    exact ⟨inR_embX γ, by rw [← map_inv]; exact inR_embX _⟩
  exact (this h).1

end Plain

section Rat
variable {E k : Type} [Field E] [Field k] (ι : E →+* k)

/- English proof (translation)
Establish `hv : v = ∑ l' : Fin N, v l' • (Pi.single l' (1 : E) : Fin N → E)`. Use function extensionality and compare the values at `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [hv]`. Rewrite using `[map_sum, Finset.sum_apply]`.

Use `Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]`.
-/
theorem apply_sum {N : ℕ} (φ : (Fin N → E) ≃ₗ[E] (Fin N → E)) (v : Fin N → E) (l : Fin N) :
    φ v l = ∑ l' : Fin N, φ (Pi.single l' 1) l * v l' := by
  have hv : v = ∑ l' : Fin N, v l' • (Pi.single l' (1 : E) : Fin N → E) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/- English proof (translation)
Use function extensionality and compare the values at `l`. Simplify using `[Loc.eN, Pi.single_apply, Fin.ext_iff]`.
-/
theorem eN_eq {N : ℕ} (u : Fin N) : Loc.eN E N u.val = Pi.single u 1 := by
  funext l; simp [Loc.eN, Pi.single_apply, Fin.ext_iff]

/- English proof (translation)
Use function extensionality and compare the values at `l`. Use `l.2` as an intermediate fact. Simplify using `only [Loc.eN, Pi.zero_apply]`. Rewrite using `[if_neg (by omega)]`.
-/
theorem eN_eq_zero {N i : ℕ} (h : N ≤ i) : Loc.eN E N i = 0 := by
  funext l
  have := l.2
  simp only [Loc.eN, Pi.zero_apply]
  rw [if_neg (by omega)]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩ l l' h`. Break down `h with ⟨ha, hb⟩ | ha` into its components or cases. Distinguish the cases in `hl : l'.val < n`. Rewrite using `[if_neg (by rintro rfl; omega)]`.

Use `h1 0 (Pi.single l' 1) (fun m hm => ?_) l (by simpa using ha)` and prove the remaining obligations. Rewrite using `[Pi.single_eq_of_ne]`. Introduce and unpack `rfl`. Conclude with `hm (by simpa using hl)`. Take `⟨i, hi⟩ : ∃ i, l'.val = n + i` from `⟨l'.val - n, by omega⟩`.

Use `h3 i l (by simp only [Set.mem_setOf_eq]; omega)` as an intermediate fact. Rewrite `this` using `[← hi, eN_eq, Pi.sub_apply, sub_eq_zero]`. Rewrite using `[this, Pi.single_apply]`. Rewrite `h2` using `[show Loc.eN E (n + c) n = Pi.single l' 1 from by rw [← eN_eq, ha]]`. Rewrite using `[h2, Pi.single_apply]`.

Introduce `h`. Use `⟨fun i v hv l hl => ?_, ?_, fun i l hl => ?_⟩` and prove the remaining obligations. Rewrite using `[apply_sum]`. Use `Finset.sum_eq_zero fun l' _ => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hl`.

Distinguish the cases in `h' : l'.val < n + i`. Rewrite using `[h l l' (Or.inl ⟨by omega, by omega⟩), if_neg (by rintro rfl; omega), zero_mul]`. Rewrite using `[hv l' h', mul_zero]`. Distinguish the cases in `hn : n < n + c`. Use `eN_eq (E := E) (⟨n, hn⟩ : Fin (n + c))` as an intermediate fact.

Rewrite using `[show Loc.eN E (n + c) n = _ from this]`. Use function extensionality and compare the values at `l`. Rewrite using `[h l _ (Or.inr rfl), Pi.single_apply]`. Rewrite using `[eN_eq_zero (by omega), map_zero]`. Simplify using `only [Set.mem_setOf_eq] at hl`.

Establish `hn : n + i < n + c` using `by have := l.2; omega`. Use `eN_eq (E := E) (⟨n + i, hn⟩ : Fin (n + c))` as an intermediate fact. Rewrite using `[show Loc.eN E (n + c) (n + i) = _ from this, Pi.sub_apply, h l _ (Or.inl ⟨by omega, by simp only; omega⟩), Pi.single_apply, sub_self]`.
-/
theorem r1cond_iff {n c : ℕ} (γ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) :
    Loc.R1cond E n c γ ↔ ∀ l l' : Fin (n + c), ((n ≤ l.val ∧ l'.val ≤ l.val) ∨ l'.val = n) →
      γ (Pi.single l' 1) l = if l = l' then 1 else 0 := by
  constructor
  · rintro ⟨h1, h2, h3⟩ l l' h
    rcases h with ⟨ha, hb⟩ | ha
    · by_cases hl : l'.val < n
      · rw [if_neg (by rintro rfl; omega)]
        refine h1 0 (Pi.single l' 1) (fun m hm => ?_) l (by simpa using ha)
        rw [Pi.single_eq_of_ne]
        rintro rfl
        exact hm (by simpa using hl)
      · obtain ⟨i, hi⟩ : ∃ i, l'.val = n + i := ⟨l'.val - n, by omega⟩
        have := h3 i l (by simp only [Set.mem_setOf_eq]; omega)
        rw [← hi, eN_eq, Pi.sub_apply, sub_eq_zero] at this
        rw [this, Pi.single_apply]
    · rw [show Loc.eN E (n + c) n = Pi.single l' 1 from by rw [← eN_eq, ha]] at h2
      rw [h2, Pi.single_apply]
  · intro h
    refine ⟨fun i v hv l hl => ?_, ?_, fun i l hl => ?_⟩
    · rw [apply_sum]
      refine Finset.sum_eq_zero fun l' _ => ?_
      simp only [Set.mem_setOf_eq] at hl
      by_cases h' : l'.val < n + i
      · rw [h l l' (Or.inl ⟨by omega, by omega⟩), if_neg (by rintro rfl; omega), zero_mul]
      · rw [hv l' h', mul_zero]
    · by_cases hn : n < n + c
      · have := eN_eq (E := E) (⟨n, hn⟩ : Fin (n + c))
        rw [show Loc.eN E (n + c) n = _ from this]
        funext l
        rw [h l _ (Or.inr rfl), Pi.single_apply]
      · rw [eN_eq_zero (by omega), map_zero]
    · simp only [Set.mem_setOf_eq] at hl
      have hn : n + i < n + c := by have := l.2; omega
      have := eN_eq (E := E) (⟨n + i, hn⟩ : Fin (n + c))
      rw [show Loc.eN E (n + c) (n + i) = _ from this, Pi.sub_apply, h l _ (Or.inl ⟨by omega, by simp only; omega⟩),
        Pi.single_apply, sub_self]

variable {A : Type} [Fintype A] [DecidableEq A] {n c : ℕ} {pos : A → ℕ}

/- English proof (translation)
Establish `h1 : ∀ a, (e (.inl a)).val < n` using `fun a => by rw [he]; exact hpos a`. Establish `h2 : ∀ i, (e (.inr i)).val = n + i.val` using `fun i => he _`. Establish `key : ∀ a b, toLoc ι e e γ.toLinearMap a b = (1 : Matrix _ _ k) a b ↔ γ (Pi.single (e b) 1) (e a) = if e a = e b then 1 else 0` using `fun a b => by`. Rewrite using `[← ι.injective.eq_iff, Matrix.one_apply]`. Simplify using `[toLoc, apply_ite ι]`.

Rewrite using `[r1cond_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun l s => ?_, fun r i hl => (key _ _).2 (h _ _ ?_)⟩` and prove the remaining obligations. Use `h1 s` as an intermediate fact.

Use `h2 l` as an intermediate fact. Rewrite using `[(key _ _).2 (h _ _ (Or.inl ⟨by omega, by omega⟩))]`. Simplify using the standard rewrite rules. Use `h2 i` as an intermediate fact. Break down `r with r | r` into its components or cases.

Simplify using `only [RootEx.lev, Sum.elim_inl, Sum.elim_inr] at hl right`. Use linear arithmetic over natural numbers and integers. Simplify using `only [RootEx.lev, Sum.elim_inr] at hl`. Use `h2 r` as an intermediate fact. Use `left`.

Use linear arithmetic over natural numbers and integers. Introduce `h l l' hl`. Take `⟨a, rfl⟩` from `e.surjective l`. Take `⟨b, rfl⟩` from `e.surjective l'`. Use `(key _ _).1 ?_` and prove the remaining obligations.

Break down `b with b | i` into its components or cases. Use `h1 b` as an intermediate fact. Break down `a with a | a` into its components or cases. Use `h1 a` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[h.1]`. Simplify using the standard rewrite rules. Use `h.2 a i ?_` and prove the remaining obligations. Use `h2 i` as an intermediate fact. Break down `a with a | a` into its components or cases.

Use `h1 a` as an intermediate fact. Simplify using `only [RootEx.lev, Sum.elim_inl, Sum.elim_inr]`. Use linear arithmetic over natural numbers and integers. Use `h2 a` as an intermediate fact. Simplify using `only [RootEx.lev, Sum.elim_inr]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem r1cond_iff_inR (hpos : ∀ a, pos a < n) {e : A ⊕ Fin c ≃ Fin (n + c)} (he : IsOrd (yPos pos n) e)
    (γ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) : Loc.R1cond E n c γ ↔ InR (toLoc ι e e γ.toLinearMap) := by
  have h1 : ∀ a, (e (.inl a)).val < n := fun a => by rw [he]; exact hpos a
  have h2 : ∀ i, (e (.inr i)).val = n + i.val := fun i => he _
  have key : ∀ a b, toLoc ι e e γ.toLinearMap a b = (1 : Matrix _ _ k) a b ↔
      γ (Pi.single (e b) 1) (e a) = if e a = e b then 1 else 0 := fun a b => by
    rw [← ι.injective.eq_iff, Matrix.one_apply]
    simp [toLoc, apply_ite ι]
  rw [r1cond_iff]
  constructor
  · intro h
    refine ⟨fun l s => ?_, fun r i hl => (key _ _).2 (h _ _ ?_)⟩
    · have := h1 s
      have := h2 l
      rw [(key _ _).2 (h _ _ (Or.inl ⟨by omega, by omega⟩))]
      simp
    · have := h2 i
      rcases r with r | r
      · simp only [RootEx.lev, Sum.elim_inl, Sum.elim_inr] at hl
        right; omega
      · simp only [RootEx.lev, Sum.elim_inr] at hl
        have := h2 r
        left; omega
  · intro h l l' hl
    obtain ⟨a, rfl⟩ := e.surjective l
    obtain ⟨b, rfl⟩ := e.surjective l'
    refine (key _ _).1 ?_
    rcases b with b | i
    · have := h1 b
      rcases a with a | a
      · have := h1 a; omega
      · rw [h.1]; simp
    · refine h.2 a i ?_
      have := h2 i
      rcases a with a | a
      · have := h1 a
        simp only [RootEx.lev, Sum.elim_inl, Sum.elim_inr]; omega
      · have := h2 a
        simp only [RootEx.lev, Sum.elim_inr]; omega

def phi {B : Type} [Fintype B] [DecidableEq B] {N : ℕ} (e : B ≃ Fin N) : ((Fin N → E) ≃ₗ[E] (Fin N → E)) →* GL B k :=
  MonoidHom.toHomUnits
    { toFun := fun γ => toLoc ι e e γ.toLinearMap
      map_one' := GlobalTheory.SymBridge.toLoc_id_square ι e
      map_mul' := fun a b => GlobalTheory.SymBridge.toLoc_comp_square ι e a.toLinearMap b.toLinearMap }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phi_val {B : Type} [Fintype B] [DecidableEq B] {N : ℕ} (e : B ≃ Fin N) (γ : (Fin N → E) ≃ₗ[E] (Fin N → E)) :
    (phi ι e γ).val = toLoc ι e e γ.toLinearMap := rfl

/- English proof (translation)
Use `⟨fun h => mem_R_of_inR ((r1cond_iff_inR ι hpos he γ).1 h.1), fun h => ⟨(r1cond_iff_inR ι hpos he γ).2 (inR_of_mem_R h), (r1cond_iff_inR ι hpos he γ⁻¹).2 ?_⟩⟩` and prove the remaining obligations. Use `inR_of_mem_R (inv_mem h)` as an intermediate fact. Rewrite `this` using `[← map_inv]`. Then use the resulting hypothesis.
-/
theorem mem_rationalFirstParabolic_iff_localGL_mem_rootExchange (hpos : ∀ a, pos a < n) {e : A ⊕ Fin c ≃ Fin (n + c)} (he : IsOrd (yPos pos n) e)
    (γ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) : γ ∈ Loc.R1 E n c ↔ phi ι e γ ∈ GlobalTheory.RootEx.R k A c 1 := by
  refine ⟨fun h => mem_R_of_inR ((r1cond_iff_inR ι hpos he γ).1 h.1), fun h => ⟨(r1cond_iff_inR ι hpos he γ).2 (inR_of_mem_R h),
    (r1cond_iff_inR ι hpos he γ⁻¹).2 ?_⟩⟩
  have := inR_of_mem_R (inv_mem h)
  rwa [← map_inv] at this

/- English proof (translation)
Establish `hd : (M.submatrix e.symm e.symm).det ≠ 0`. Rewrite using `[det_submatrix_equiv_self]`. Introduce `h`. Use `u.det_ne_zero` as an intermediate fact. Rewrite `this` using `[hu, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]`.

Conclude with `this rfl`. Use `⟨Matrix.toLinearEquiv' _ (invertibleOfIsUnitDet _ (Ne.isUnit hd)), Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hu, phi_val]`. Use extensionality with `a b`. Simplify using `only [toLoc, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply, mulVec_single_one, Matrix.map_apply]`.

Simplify using the standard rewrite rules.
-/
theorem exists_phi {B : Type} [Fintype B] [DecidableEq B] {N : ℕ} (e : B ≃ Fin N) (M : Matrix B B E) (u : GL B k)
    (hu : u.val = M.map ι) : ∃ γ, phi ι e γ = u := by
  have hd : (M.submatrix e.symm e.symm).det ≠ 0 := by
    rw [det_submatrix_equiv_self]
    intro h
    have := u.det_ne_zero
    rw [hu, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero] at this
    exact this rfl
  refine ⟨Matrix.toLinearEquiv' _ (invertibleOfIsUnitDet _ (Ne.isUnit hd)), Units.ext ?_⟩
  rw [hu, phi_val]
  ext a b
  simp only [toLoc, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply, mulVec_single_one, Matrix.map_apply]
  simp

end Rat

section Dense
variable {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k)
  {B : Type} [Fintype B] [DecidableEq B]

/- English proof (translation)
Set `T : (B × B → k) → Matrix B B k` to `fun x => Matrix.of fun a b => if M a b = (1 : Matrix B B k) a b then (1 : Matrix B B k) a b else x (a, b)`. Establish `hT : Continuous T`. Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [T, Matrix.of_apply]`. Use `split_ifs`.

Conclude with `continuous_const`. Conclude with `continuous_apply _`. Establish `hd : DenseRange (Pi.map fun _ : B × B => (ι : E → k))` using `DenseRange.piMap fun _ => hι`. Take `⟨x, hx⟩` from `hd.exists_mem_open (hU.preimage hT) ⟨fun p => M p.1 p.2, by`. Establish `: T (fun p => M p.1 p.2) = M`.

Use extensionality with `a b`. Simplify using `only [T, Matrix.of_apply]`. Use `split_ifs with h`. Conclude with `h.symm`. Both sides reduce to the same expression.

Rewrite using `[Set.mem_preimage, this]⟩` and apply the resulting hypothesis. Establish `e : (Matrix.of fun a b => if M a b = (1 : Matrix B B k) a b then (1 : Matrix B B E) a b else x (a, b)).map ι = T (Pi.map (fun _ : B × B => (ι : E → k)) x)`. Use extensionality with `a b`. Simplify using `only [T, Matrix.of_apply, Matrix.map_apply, Pi.map_apply]`. Use `split_ifs`.

Simplify using `[Matrix.one_apply, apply_ite ι]`. Both sides reduce to the same expression. Use `⟨_, by rw [e]; exact hx, fun a b h => ?_⟩` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `if_pos h`.
-/
theorem exists_approx (hι : DenseRange ι) (M : Matrix B B k) {U : Set (Matrix B B k)} (hU : IsOpen U) (hM : M ∈ U) :
    ∃ M₀ : Matrix B B E, M₀.map ι ∈ U ∧ ∀ a b, M a b = (1 : Matrix B B k) a b → M₀.map ι a b = (1 : Matrix B B k) a b := by
  classical
  let T : (B × B → k) → Matrix B B k := fun x => Matrix.of fun a b =>
    if M a b = (1 : Matrix B B k) a b then (1 : Matrix B B k) a b else x (a, b)
  have hT : Continuous T := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [T, Matrix.of_apply]
    split_ifs
    · exact continuous_const
    · exact continuous_apply _
  have hd : DenseRange (Pi.map fun _ : B × B => (ι : E → k)) := DenseRange.piMap fun _ => hι
  obtain ⟨x, hx⟩ := hd.exists_mem_open (hU.preimage hT) ⟨fun p => M p.1 p.2, by
    have : T (fun p => M p.1 p.2) = M := by
      ext a b
      simp only [T, Matrix.of_apply]
      split_ifs with h
      · exact h.symm
      · rfl
    rwa [Set.mem_preimage, this]⟩
  have e : (Matrix.of fun a b => if M a b = (1 : Matrix B B k) a b then (1 : Matrix B B E) a b else x (a, b)).map ι =
      T (Pi.map (fun _ : B × B => (ι : E → k)) x) := by
    ext a b
    simp only [T, Matrix.of_apply, Matrix.map_apply, Pi.map_apply]
    split_ifs
    · simp [Matrix.one_apply, apply_ite ι]
    · rfl
  refine ⟨_, by rw [e]; exact hx, fun a b h => ?_⟩
  rw [e]
  exact if_pos h

/- English proof (translation)
Rewrite using `[DoubleCoset.eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, κ, hκ, rfl⟩`. Conclude with `⟨_, (mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι hpos he r).1 hr, _, (hJ₀ κ).2 hκ, by rw [map_mul, map_mul]⟩`. Introduce and unpack `⟨r, hr, κ, hκ, h⟩ set g := phi ι e γ with hg`.

Establish `hU : IsOpen {M : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k | MaxM ((g⁻¹).val * M * (r * g).val - 1)}`. Simplify using `only [MaxM, Set.setOf_forall]`. Use `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_` and prove the remaining obligations. Conclude with `IsOpen.preimage (f := fun M : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k => ((g⁻¹).val * M * (r * g).val - 1) i j) (t := {z | valuation k z < 1}) (by fun_prop) (by simpa using (valuation k).isOpen_ball 1)`. Take `⟨M₀, h1, h2⟩` from `exists_approx ι hι (r⁻¹).val hU (by`.

Express the relevant statement in the definitionally equal form `MaxM _`. Rewrite using `[← Units.val_mul, ← Units.val_mul, show g⁻¹ * r⁻¹ * (r * g) = 1 by group, Units.val_one, sub_self]`. Conclude with `maxM_zero)`. Take `⟨u, hu, eu⟩` from `exists_mem_KOne h1`. Establish `ev : (g * u * (r * g)⁻¹).val = M₀.map ι`.

Rewrite using `[Units.val_mul, Units.val_mul, eu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Take `⟨ρ, hρ⟩` from `exists_phi ι e M₀ _ ev`. Establish `hi` using `inR_of_mem_R (inv_mem hr)`. Establish `hρR : ρ ∈ Loc.R1 E n c`. Rewrite using `[mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι hpos he, hρ]`.

Use `mem_R_of_inR ?_` and prove the remaining obligations. Rewrite using `[ev]`. Conclude with `⟨fun l s => by rw [h2 _ _ (by rw [hi.1]; simp)]; simp, fun a i hl => h2 _ _ (hi.2 a i hl)⟩`. Use `⟨ρ⁻¹, inv_mem hρR, γ⁻¹ * ρ * γ', (hJ₀ _).1 ?_, by group⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_inv, hρ, h, ← hg, show g⁻¹ * (g * u * (r * g)⁻¹) * (r * g * κ) = u * κ by group]`.

Conclude with `mul_mem (hJ hu) hκ`.
-/
theorem dc_iff (hι : DenseRange ι) {A : Type} [Fintype A] [DecidableEq A] {n c : ℕ} {pos : A → ℕ} (hpos : ∀ a, pos a < n)
    {e : A ⊕ Fin c ≃ Fin (n + c)} (he : IsOrd (yPos pos n) e) (J : Subgroup (GL (A ⊕ Fin c) k)) (hJ : KOne k _ ≤ J)
    (J₀ : Subgroup ((Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E))) (hJ₀ : ∀ γ, phi ι e γ ∈ J ↔ γ ∈ J₀)
    (γ γ' : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) :
    (∃ r ∈ Loc.R1 E n c, ∃ κ ∈ J₀, γ' = r * γ * κ) ↔ DoubleCoset.mk (GlobalTheory.RootEx.R k A c 1) J (phi ι e γ) =
      DoubleCoset.mk (GlobalTheory.RootEx.R k A c 1) J (phi ι e γ') := by
  rw [DoubleCoset.eq]
  constructor
  · rintro ⟨r, hr, κ, hκ, rfl⟩
    exact ⟨_, (mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι hpos he r).1 hr, _, (hJ₀ κ).2 hκ, by rw [map_mul, map_mul]⟩
  · rintro ⟨r, hr, κ, hκ, h⟩
    set g := phi ι e γ with hg
    have hU : IsOpen {M : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k | MaxM ((g⁻¹).val * M * (r * g).val - 1)} := by
      simp only [MaxM, Set.setOf_forall]
      refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
      exact IsOpen.preimage (f := fun M : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k => ((g⁻¹).val * M * (r * g).val - 1) i j)
        (t := {z | valuation k z < 1}) (by fun_prop) (by simpa using (valuation k).isOpen_ball 1)
    obtain ⟨M₀, h1, h2⟩ := exists_approx ι hι (r⁻¹).val hU (by
      change MaxM _
      rw [← Units.val_mul, ← Units.val_mul, show g⁻¹ * r⁻¹ * (r * g) = 1 by group, Units.val_one, sub_self]
      exact maxM_zero)
    obtain ⟨u, hu, eu⟩ := exists_mem_KOne h1
    have ev : (g * u * (r * g)⁻¹).val = M₀.map ι := by
      rw [Units.val_mul, Units.val_mul, eu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul,
        Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    obtain ⟨ρ, hρ⟩ := exists_phi ι e M₀ _ ev
    have hi := inR_of_mem_R (inv_mem hr)
    have hρR : ρ ∈ Loc.R1 E n c := by
      rw [mem_rationalFirstParabolic_iff_localGL_mem_rootExchange ι hpos he, hρ]
      refine mem_R_of_inR ?_
      rw [ev]
      exact ⟨fun l s => by rw [h2 _ _ (by rw [hi.1]; simp)]; simp, fun a i hl => h2 _ _ (hi.2 a i hl)⟩
    refine ⟨ρ⁻¹, inv_mem hρR, γ⁻¹ * ρ * γ', (hJ₀ _).1 ?_, by group⟩
    rw [map_mul, map_mul, map_inv, hρ, h, ← hg, show g⁻¹ * (g * u * (r * g)⁻¹) * (r * g * κ) = u * κ by group]
    exact mul_mem (hJ hu) hκ

end Dense

section Lat
variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h l l'`. Establish `h1` using `h (((q : E) ^ ex l'.1) • (Pi.single l' (1 : E) : Sp E N)) (by`. Rewrite using `[StabRef.mem_sclLat]`. Introduce `l`.

Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `h : l = l'`. Substitute `h` using the available equality. Rewrite using `[Pi.single_eq_same, mul_one, inv_mul_cancel₀ (zpow_ne_zero _ hq0)]`. Simplify using `using IntAt.coe P 1`.

Rewrite using `[Pi.single_eq_of_ne h, mul_zero, mul_zero]`. Conclude with `StabRef.intAt_zero)`. Establish `h2` using `(StabRef.mem_sclLat _ _).1 h1 l`. Rewrite `h2` using `[map_smul, Pi.smul_apply, smul_eq_mul]`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[zpow_sub₀ hq0]`. Expand and normalize the polynomial expressions, which then agree. Introduce `hκ v hv`. Rewrite `hv`, the goal using `[StabRef.mem_sclLat]`. Introduce `l`.

Rewrite using `[apply_sum κ v l, Finset.mul_sum]`. Use `StabRef.intAt_sum _ _ fun l' _ => ?_` and prove the remaining obligations. Use `(hκ l l').mul (hv l') using 1` and compare the differences between its conclusion and the goal. Rewrite using `[zpow_sub₀ hq0]`. Establish `h1 : (q : E) ^ ex l'.1 ≠ 0` using `zpow_ne_zero _ hq0`.

Clear the denominators using the available nonvanishing facts.
-/
theorem map_sclLat_iff (hq0 : (q : E) ≠ 0) {N : ℕ} (ex : ℕ → ℤ) (κ : Sp E N ≃ₗ[E] Sp E N) :
    (∀ v ∈ LocE.sclLat P q N ex, κ v ∈ LocE.sclLat P q N ex) ↔
      ∀ l l' : Fin N, IntAt P (κ (Pi.single l' 1) l * (q : E) ^ (ex l'.1 - ex l.1)) := by
  constructor
  · intro h l l'
    have h1 := h (((q : E) ^ ex l'.1) • (Pi.single l' (1 : E) : Sp E N)) (by
      rw [StabRef.mem_sclLat]
      intro l
      rw [Pi.smul_apply, smul_eq_mul]
      by_cases h : l = l'
      · subst h
        rw [Pi.single_eq_same, mul_one, inv_mul_cancel₀ (zpow_ne_zero _ hq0)]
        simpa using IntAt.coe P 1
      · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]
        exact StabRef.intAt_zero)
    have h2 := (StabRef.mem_sclLat _ _).1 h1 l
    rw [map_smul, Pi.smul_apply, smul_eq_mul] at h2
    convert h2 using 1
    rw [zpow_sub₀ hq0]
    ring
  · intro hκ v hv
    rw [StabRef.mem_sclLat] at hv ⊢
    intro l
    rw [apply_sum κ v l, Finset.mul_sum]
    refine StabRef.intAt_sum _ _ fun l' _ => ?_
    convert (hκ l l').mul (hv l') using 1
    rw [zpow_sub₀ hq0]
    have h1 : (q : E) ^ ex l'.1 ≠ 0 := zpow_ne_zero _ hq0
    field_simp

/- English proof (translation)
Use `⟨fun h => ⟨fun v hv => (h v).2 hv, fun v hv => ((inv_mem h : κ⁻¹ ∈ stabL E N L) v).2 hv⟩, fun h v => ⟨fun hv => ?_, h.1 v⟩⟩` and prove the remaining obligations. Use `h.2 _ hv` as an intermediate fact. Rewrite `this` using `[show κ⁻¹ (κ v) = v from LinearEquiv.symm_apply_apply κ v]`. Then use the resulting hypothesis.
-/
theorem mem_stabL_iff {N : ℕ} (L : Submodule (𝓞 E) (Sp E N)) (κ : Sp E N ≃ₗ[E] Sp E N) :
    κ ∈ stabL E N L ↔ (∀ v ∈ L, κ v ∈ L) ∧ ∀ v ∈ L, κ⁻¹ v ∈ L := by
  refine ⟨fun h => ⟨fun v hv => (h v).2 hv, fun v hv => ((inv_mem h : κ⁻¹ ∈ stabL E N L) v).2 hv⟩, fun h v => ⟨fun hv => ?_, h.1 v⟩⟩
  have := h.2 _ hv
  rwa [show κ⁻¹ (κ v) = v from LinearEquiv.symm_apply_apply κ v] at this

/- English proof (translation)
Use extensionality with `v`. Rewrite using `[StabRef.mem_sclLat, stdAt, StabRef.mem_locStd]`. Simplify using the standard rewrite rules.
-/
theorem stdAt_eq (N : ℕ) : stdAt E N P = LocE.sclLat P q N 0 := by
  ext v
  rw [StabRef.mem_sclLat, stdAt, StabRef.mem_locStd]
  simp

variable (P q) in

def Par (kj n c : ℕ) (κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) : Prop :=
  (∀ l l', IntAt P (κ (Pi.single l' 1) l)) ∧ ∀ l l' : Fin (n + c), (kj ≤ l.1 ∧ l.1 < n) → ¬ (kj ≤ l'.1 ∧ l'.1 < n) →
    IntAt P (κ (Pi.single l' 1) l / (q : E))

/- English proof (translation)
Rewrite using `[stdAt_eq (q := q), LocE.parL, map_sclLat_iff hq0, map_sclLat_iff hq0, Par]`. Simplify using `only [Pi.zero_apply, sub_self, zpow_zero, mul_one]`. Use `and_congr_right fun h => ⟨fun h' l l' => ?_, fun h' l l' h1 h2 => ?_⟩` and prove the remaining obligations. Use `split_ifs with h1 h2 h2`. Simplify using `using h l l'`.

Simplify using `using (h l l').mul (IntAt.coe P (q : 𝓞 E))`. Simplify `h' l l' h2 h1` using `[div_eq_mul_inv]`. Simplify using `using h l l'`. Use `h' l l'` as an intermediate fact. Rewrite `this` using `[if_pos h1, if_neg h2]`.

Simplify `this` using `[div_eq_mul_inv]`.
-/
theorem par_iff (hq0 : (q : E) ≠ 0) (kj n c : ℕ) (κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    Par P q kj n c κ ↔ (∀ v ∈ stdAt E (n + c) P, κ v ∈ stdAt E (n + c) P) ∧
      ∀ v ∈ LocE.parL P q kj n c, κ v ∈ LocE.parL P q kj n c := by
  rw [stdAt_eq (q := q), LocE.parL, map_sclLat_iff hq0, map_sclLat_iff hq0, Par]
  simp only [Pi.zero_apply, sub_self, zpow_zero, mul_one]
  refine and_congr_right fun h => ⟨fun h' l l' => ?_, fun h' l l' h1 h2 => ?_⟩
  · split_ifs with h1 h2 h2
    · simpa using h l l'
    · simpa using (h l l').mul (IntAt.coe P (q : 𝓞 E))
    · simpa [div_eq_mul_inv] using h' l l' h2 h1
    · simpa using h l l'
  · have := h' l l'
    rw [if_pos h1, if_neg h2] at this
    simpa [div_eq_mul_inv] using this

/- English proof (translation)
Rewrite using `[LocE.JQ, Subgroup.mem_inf, mem_stabL_iff, mem_stabL_iff, par_iff hq0, par_iff hq0]`. The claim follows by propositional logic.
-/
theorem mem_JQ_iff [StarRing E] (hq0 : (q : E) ≠ 0) (kj n c : ℕ) (κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    κ ∈ LocE.JQ P q kj n c ↔ Par P q kj n c κ ∧ Par P q kj n c κ⁻¹ := by
  rw [LocE.JQ, Subgroup.mem_inf, mem_stabL_iff, mem_stabL_iff, par_iff hq0, par_iff hq0]
  tauto

end Lat

section Level
variable {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} {κ τ j c s n : ℕ}

/- English proof (translation)
Take `⟨y, rfl⟩` from `(stdOrd (Fin κ) (Fin τ) j c h).symm.surjective x`. Rewrite using `[Equiv.apply_symm_apply]`. Break down `y with ((i | i) | p) | i` into its components or cases. Rewrite using `[(Equiv.symm_apply_eq _).2 (stdOrd_eps _ _ j c h i).symm]`. Use `i.2` as an intermediate fact.

Simplify using `[yPos, xPos]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[(Equiv.symm_apply_eq _).2 (stdOrd_f _ _ j c h i).symm]`. Simplify using `[yPos, xPos]`. Rewrite using `[(Equiv.symm_apply_eq _).2 (stdOrd_d _ _ j c h p).symm]`.

Use `GlobalTheory.SymBridge.Coords.xPos_lt (κ := κ) (.inr p)` as an intermediate fact. Simplify using `only [yPos, xPos, Sum.elim_inl, Sum.isRight_inr, iff_true] at this ⊢`. Use linear arithmetic over natural numbers and integers. Rewrite using `[(Equiv.symm_apply_eq _).2 (standardOrderExtendedBasis_apply_low_block _ _ j c h i).symm]`. Simplify using `[yPos]`.
-/
theorem pos_stdOrd (h : j + c = s + 1) (hn : n = κ + j * (τ + 1)) (x : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) :
    (κ + j ≤ yPos xPos n (stdOrd (Fin κ) (Fin τ) j c h x) ∧ yPos xPos n (stdOrd (Fin κ) (Fin τ) j c h x) < n) ↔
      x.isRight = true := by
  obtain ⟨y, rfl⟩ := (stdOrd (Fin κ) (Fin τ) j c h).symm.surjective x
  rw [Equiv.apply_symm_apply]
  rcases y with ((i | i) | p) | i
  · rw [(Equiv.symm_apply_eq _).2 (stdOrd_eps _ _ j c h i).symm]
    have := i.2
    simp [yPos, xPos]; omega
  · rw [(Equiv.symm_apply_eq _).2 (stdOrd_f _ _ j c h i).symm]
    simp [yPos, xPos]
  · rw [(Equiv.symm_apply_eq _).2 (stdOrd_d _ _ j c h p).symm]
    have := GlobalTheory.SymBridge.Coords.xPos_lt (κ := κ) (.inr p)
    simp only [yPos, xPos, Sum.elim_inl, Sum.isRight_inr, iff_true] at this ⊢
    omega
  · rw [(Equiv.symm_apply_eq _).2 (standardOrderExtendedBasis_apply_low_block _ _ j c h i).symm]
    simp [yPos]

/- English proof (translation)
Use `set o := stdOrd (Fin κ) (Fin τ) j c h`. Establish `hv : ∀ x y, ((reGL o).symm (phi ι e γ)).val x y = ι (γ (Pi.single (e (o y)) 1) (e (o x)))` using `fun _ _ => rfl`. Use `and_congr ⟨fun H x y => (hc.int _).2 (H _ _), fun H l l' => ?_⟩ ⟨fun H x y => ?_, fun H l l' h1 h2 => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `(o.trans e).surjective l`. Take `⟨y, rfl⟩` from `(o.trans e).surjective l'`.

Conclude with `(hc.int _).1 (H x y)`. Use `(GlobalTheory.SymBridge.ComplRes.v_div_q hc hu _).2 (H (e (o (.inr x))) (e (o (.inl y))) ?_ ?_)` and prove the remaining obligations. Rewrite using `[he, pos_stdOrd h hn]`. Both sides reduce to the same expression. Rewrite using `[he, pos_stdOrd h hn]`.

Simplify using the standard rewrite rules. Take `⟨x, rfl⟩` from `(o.trans e).surjective l`. Take `⟨y, rfl⟩` from `(o.trans e).surjective l'`. Rewrite `h1`, `h2` using `[Equiv.trans_apply, he, pos_stdOrd h hn]`. Break down `x with x | x` into its components or cases.

Simplify using `at h1`. Break down `y with y | y` into its components or cases. Conclude with `(GlobalTheory.SymBridge.ComplRes.v_div_q hc hu _).1 (H x y)`. Simplify using `at h2`.
-/
theorem par_iff_mat (hc : IsCompl P q ι ϖ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (h : j + c = s + 1) (hn : n = κ + j * (τ + 1))
    {e : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin (n + c)} (he : IsOrd (yPos xPos n) e) (γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    Par P q (κ + j) n c γ ↔ IntM ((reGL (stdOrd (Fin κ) (Fin τ) j c h)).symm (phi ι e γ)).val ∧
      MaxM ((reGL (stdOrd (Fin κ) (Fin τ) j c h)).symm (phi ι e γ)).val.toBlocks₂₁ := by
  set o := stdOrd (Fin κ) (Fin τ) j c h
  have hv : ∀ x y, ((reGL o).symm (phi ι e γ)).val x y = ι (γ (Pi.single (e (o y)) 1) (e (o x))) := fun _ _ => rfl
  refine and_congr ⟨fun H x y => (hc.int _).2 (H _ _), fun H l l' => ?_⟩ ⟨fun H x y => ?_, fun H l l' h1 h2 => ?_⟩
  · obtain ⟨x, rfl⟩ := (o.trans e).surjective l
    obtain ⟨y, rfl⟩ := (o.trans e).surjective l'
    exact (hc.int _).1 (H x y)
  · refine (GlobalTheory.SymBridge.ComplRes.v_div_q hc hu _).2 (H (e (o (.inr x))) (e (o (.inl y))) ?_ ?_)
    · rw [he, pos_stdOrd h hn]; rfl
    · rw [he, pos_stdOrd h hn]; simp
  · obtain ⟨x, rfl⟩ := (o.trans e).surjective l
    obtain ⟨y, rfl⟩ := (o.trans e).surjective l'
    rw [Equiv.trans_apply, he, pos_stdOrd h hn] at h1 h2
    rcases x with x | x
    · simp at h1
    rcases y with y | y
    · exact (GlobalTheory.SymBridge.ComplRes.v_div_q hc hu _).1 (H x y)
    · simp at h2

/- English proof (translation)
Rewrite using `[mem_JQ_iff (GlobalTheory.SymBridge.ComplRes.q_ne_zero hc), par_iff_mat hc hu h hn he, par_iff_mat hc hu h hn he, map_inv, map_inv]`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Establish `H1` using `mem_parahoric.1 H`. Establish `H2` using `mem_parahoric.1 (inv_mem H)`.

Conclude with `⟨⟨intM_of_mem_KO H1.1, H1.2⟩, intM_of_mem_KO H2.1, H2.2⟩`. Introduce `H`. Conclude with `mem_parahoric.2 ⟨mem_KO.2 ⟨H.1.1, H.2.1⟩, H.1.2⟩`.
-/
theorem mem_par_iff (hc : IsCompl P q ι ϖ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (h : j + c = s + 1) (hn : n = κ + j * (τ + 1))
    {e : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin (n + c)} (he : IsOrd (yPos xPos n) e) {δ : kˣ →* ℂˣ} (hδ : IsTame δ)
    (γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    (reGL (stdOrd (Fin κ) (Fin τ) j c h)).symm (phi ι e γ) ∈ (parahoric _ (Fin j × Fin τ) δ hδ).J ↔
      γ ∈ LocE.JQ P q (κ + j) n c := by
  rw [mem_JQ_iff (GlobalTheory.SymBridge.ComplRes.q_ne_zero hc), par_iff_mat hc hu h hn he, par_iff_mat hc hu h hn he, map_inv, map_inv]
  constructor
  · intro H
    have H1 := mem_parahoric.1 H
    have H2 := mem_parahoric.1 (inv_mem H)
    exact ⟨⟨intM_of_mem_KO H1.1, H1.2⟩, intM_of_mem_KO H2.1, H2.2⟩
  · intro H
    exact mem_parahoric.2 ⟨mem_KO.2 ⟨H.1.1, H.2.1⟩, H.1.2⟩

/- English proof (translation)
Establish `hm : j * τ = n - (κ + j)`. Establish `: j * (τ + 1) = j * τ + j` using `by ring`. Use linear arithmetic over natural numbers and integers. Set `f : Fin j × Fin τ ≃ Fin (n - (κ + j))` to `finProdFinEquiv.trans (finCongr hm)`. Establish `hf : ∀ p, κ + j + (f p).1 = (e (.inl (.inr p))).1` using `fun p => by`.

Rewrite using `[he]`. Simplify using `[f, yPos, xPos, finProdFinEquiv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[RingHom.map_det, ← det_submatrix_equiv_self f]`. Use `congr 1`.

Use extensionality with `a b`. Simplify using `only [RingHom.mapMatrix_apply, submatrix_apply, Matrix.map_apply, Matrix.of_apply]`. Rewrite using `[hf, hf, eN_eq, Loc.atN, dif_pos (Fin.is_lt _)]`. Both sides reduce to the same expression.
-/
theorem det_block (h : j + c = s + 1) (hn : n = κ + j * (τ + 1))
    {e : XIx (Fin κ) (Fin τ) j ⊕ Fin c ≃ Fin (n + c)} (he : IsOrd (yPos xPos n) e) (γ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    ((reGL (stdOrd (Fin κ) (Fin τ) j c h)).symm (phi ι e γ)).val.toBlocks₂₂.det =
      ι (Matrix.det (Matrix.of fun a b : Fin (n - (κ + j)) =>
        Loc.atN (γ.toLinearMap (Loc.eN E (n + c) (κ + j + b.1))) (κ + j + a.1))) := by
  have hm : j * τ = n - (κ + j) := by
    have : j * (τ + 1) = j * τ + j := by ring
    omega
  let f : Fin j × Fin τ ≃ Fin (n - (κ + j)) := finProdFinEquiv.trans (finCongr hm)
  have hf : ∀ p, κ + j + (f p).1 = (e (.inl (.inr p))).1 := fun p => by
    rw [he]
    simp [f, yPos, xPos, finProdFinEquiv]
    ring
  rw [RingHom.map_det, ← det_submatrix_equiv_self f]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, submatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [hf, hf, eN_eq, Loc.atN, dif_pos (Fin.is_lt _)]
  rfl

end Level

/- English proof (translation)
Introduce `X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν _ _ hA j c h γ g hg`. Establish `hc : c = cOf R j` using `by have := hA.steps; unfold cOf; omega`. Substitute `hc` using the available equality. Take `⟨e, he, hg⟩` from `hg`. Take `rfl : g = phi ι e γ` from `Units.ext hg`.

Establish `hn : R.N j = R.k + j * (R.t + 1)` using `rfl`. Use `set o := stdOrd (Fin R.k) (Fin R.t) j (cOf R j) h with ho`. Establish `hconj : ∀ g : GL _ k, (plainFrame (k` using `k) o).conj.symm g = (reGL o).symm g := fun g => by`. Rewrite using `[MulEquiv.symm_apply_eq, LatFrame.conj_apply, show (plainFrame (k := k) o).bas = 1 from rfl, show (plainFrame (k := k) o).ord = o from rfl, MulEquiv.apply_symm_apply]`. Simplify using the standard rewrite rules.

Establish `hJ : ∀ g, g ∈ ((W.T s R).lev j (cOf R j) h).J ↔ (reGL o).symm g ∈ (parahoric _ (Fin j × Fin R.t) W.δ W.tame).J` using `fun g => by rw [← hconj]; rfl`. Establish `hmem : ∀ γ : AutY X R j, phi ι e γ ∈ ((W.T s R).lev j (cOf R j) h).J ↔ γ ∈ Jat (Pr` using `Pr) cst.sharp j P.1 := fun γ => by`. Rewrite using `[hJ, Jat, if_neg hA.nmem]`. Conclude with `mem_par_iff hA.compl W.unif h hn he W.tame γ`. Use `⟨hmem γ, fun hg' => ?_, fun _ γ' g' hg' => ?_⟩` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `mem_parahoric.1 ((hJ _).1 hg')`. Take `⟨-, D, hD, eD⟩` from `exists_diag_blocks h1 h2`. Establish `e1 : ((W.T s R).lev j (cOf R j) h).lam ⟨_, hg'⟩ = W.δ (Matrix.GeneralLinearGroup.det D)` using `parahoric_lam (δ := W.δ) (hδ := W.tame) ⟨(plainFrame (k := k) o).conj.symm (phi ι e γ), hg'⟩ D (eD.trans (by rw [← hconj]))`. Establish `e2` using `det_block (ι := ι) h hn he γ`. Rewrite `e2` using `[← eD, ← Matrix.GeneralLinearGroup.val_det_apply]`.

Establish `hv` using `valuation_det_of_mem_KO hD`. Rewrite `hv` using `[e2]`. Establish `hi` using `GlobalTheory.SymBridge.ComplRes.intAt_of_v hA.compl hv.le`. Rewrite using `[e1, hA.del _ _ hi ((GlobalTheory.SymBridge.ComplRes.v_eq_one_iff_red hA.compl W.unif hi).1 hv) e2, lamRow, if_neg hA.nmem, LocE.lamQB, map_inv₀]`. Take `⟨e', he', hg'⟩` from `hg'`.

Take `rfl : e' = e` from `Equiv.ext fun a => Fin.ext ((he' a).trans (he a).symm)`. Take `rfl : g' = phi ι e' γ'` from `Units.ext hg'`. Conclude with `dc_iff ι hA.compl.dense (fun a => GlobalTheory.SymBridge.Coords.xPos_lt a) he _ (fun u hu => (hJ u).2 (((parahoric _ (Fin j × Fin R.t) W.δ W.tame).reindex o).KOne_le hu)) _ hmem γ γ'`.
-/
theorem levelAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → LevelAgree Ch sel mu cst σ₀ P ι s W := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν _ _ hA j c h γ g hg
  have hc : c = cOf R j := by have := hA.steps; unfold cOf; omega
  subst hc
  obtain ⟨e, he, hg⟩ := hg
  obtain rfl : g = phi ι e γ := Units.ext hg
  have hn : R.N j = R.k + j * (R.t + 1) := rfl
  set o := stdOrd (Fin R.k) (Fin R.t) j (cOf R j) h with ho
  have hconj : ∀ g : GL _ k, (plainFrame (k := k) o).conj.symm g = (reGL o).symm g := fun g => by
    rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply, show (plainFrame (k := k) o).bas = 1 from rfl,
      show (plainFrame (k := k) o).ord = o from rfl, MulEquiv.apply_symm_apply]
    simp
  have hJ : ∀ g, g ∈ ((W.T s R).lev j (cOf R j) h).J ↔ (reGL o).symm g ∈ (parahoric _ (Fin j × Fin R.t) W.δ W.tame).J :=
    fun g => by rw [← hconj]; rfl
  have hmem : ∀ γ : AutY X R j, phi ι e γ ∈ ((W.T s R).lev j (cOf R j) h).J ↔ γ ∈ Jat (Pr := Pr) cst.sharp j P.1 := fun γ => by
    rw [hJ, Jat, if_neg hA.nmem]
    exact mem_par_iff hA.compl W.unif h hn he W.tame γ
  refine ⟨hmem γ, fun hg' => ?_, fun _ γ' g' hg' => ?_⟩
  · obtain ⟨h1, h2⟩ := mem_parahoric.1 ((hJ _).1 hg')
    obtain ⟨-, D, hD, eD⟩ := exists_diag_blocks h1 h2
    have e1 : ((W.T s R).lev j (cOf R j) h).lam ⟨_, hg'⟩ = W.δ (Matrix.GeneralLinearGroup.det D) :=
      parahoric_lam (δ := W.δ) (hδ := W.tame) ⟨(plainFrame (k := k) o).conj.symm (phi ι e γ), hg'⟩ D
        (eD.trans (by rw [← hconj]))
    have e2 := det_block (ι := ι) h hn he γ
    rw [← eD, ← Matrix.GeneralLinearGroup.val_det_apply] at e2
    have hv := valuation_det_of_mem_KO hD
    rw [e2] at hv
    have hi := GlobalTheory.SymBridge.ComplRes.intAt_of_v hA.compl hv.le
    rw [e1, hA.del _ _ hi ((GlobalTheory.SymBridge.ComplRes.v_eq_one_iff_red hA.compl W.unif hi).1 hv) e2, lamRow, if_neg hA.nmem,
      LocE.lamQB, map_inv₀]
  · obtain ⟨e', he', hg'⟩ := hg'
    obtain rfl : e' = e := Equiv.ext fun a => Fin.ext ((he' a).trans (he a).symm)
    obtain rfl : g' = phi ι e' γ' := Units.ext hg'
    exact dc_iff ι hA.compl.dense (fun a => GlobalTheory.SymBridge.Coords.xPos_lt a) he _
      (fun u hu => (hJ u).2 (((parahoric _ (Fin j × Fin R.t) W.δ W.tame).reindex o).KOne_le hu)) _ hmem γ γ'

end GlobalTheory.TwBridge.Lev
