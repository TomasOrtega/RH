import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.StartForm

/- English proof (translation)
The claim follows from `| 0, _, _, _, _ => by simp | n + 1, f, g, hc, h1 => by have ih := prod_mul_prod_eq_one n (fun i => f i.succ) (fun i => g i.succ) (fun i j => hc _ _) (fun i => h1 _) have hcm : Commute (List.ofFn fun i : Fin n => f i.succ).prod (g 0) := by refine Commute.list_prod_left _ _ fun x h …`.
-/
theorem prod_mul_prod_eq_one {A : Type} [Ring A] : ∀ (n : ℕ) (f g : Fin n → A),
    (∀ i j, Commute (f i) (g j)) → (∀ i, f i * g i = 1) → (List.ofFn f).prod * (List.ofFn g).prod = 1
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, hc, h1 => by
    have ih := prod_mul_prod_eq_one n (fun i => f i.succ) (fun i => g i.succ) (fun i j => hc _ _) (fun i => h1 _)
    have hcm : Commute (List.ofFn fun i : Fin n => f i.succ).prod (g 0) := by
      refine Commute.list_prod_left _ _ fun x hx => ?_
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact hc _ _
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc, ← mul_assoc _ (g 0), hcm.eq,
      mul_assoc, ih, mul_one, h1]

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

/- English proof (translation)
Proceed by induction on `hx using Submonoid.closure_induction with`. Consider the case `mem x hx`. Proceed by induction on `hy using Submonoid.closure_induction with`. Consider the case `mem y hy => exact L.fns_comm x hx y hy`. Consider the case `one => exact Commute.one_right _`.

Consider the case `mul a b _ _ ha hb => exact ha.mul_right hb`. Consider the case `one => exact Commute.one_left _`. Consider the case `mul a b _ _ ha hb => exact ha.mul_left hb`.
-/
theorem comm_of_closure (L : LevelData A r) {x y : A} (hx : x ∈ Submonoid.closure L.fns)
    (hy : y ∈ Submonoid.closure L.fns) : Commute x y := by
  induction hx using Submonoid.closure_induction with
  | mem x hx =>
    induction hy using Submonoid.closure_induction with
    | mem y hy => exact L.fns_comm x hx y hy
    | one => exact Commute.one_right _
    | mul a b _ _ ha hb => exact ha.mul_right hb
  | one => exact Commute.one_left _
  | mul a b _ _ ha hb => exact ha.mul_left hb

/- English proof (translation)
Use `Submonoid.list_prod_mem _ fun x hx => ?_` and prove the remaining obligations. Take `⟨i, rfl⟩` from `(List.mem_ofFn' _ _).1 hx`. Conclude with `Submonoid.subset_closure (hf i)`.
-/
theorem prod_mem (L : LevelData A r) (f : Fin r → A) (hf : ∀ i, f i ∈ L.fns) :
    (List.ofFn f).prod ∈ Submonoid.closure L.fns := by
  refine Submonoid.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  exact Submonoid.subset_closure (hf i)

/- English proof (translation)
Establish `mc : ∀ i, L.c i ∈ L.fns` using `fun i => by simp [LevelData.fns]`. Establish `mci : ∀ i, L.ci i ∈ L.fns` using `fun i => by simp [LevelData.fns]`. Establish `mcb : ∀ i, L.cb i ∈ L.fns` using `fun i => by simp [LevelData.fns]`. Establish `mcbi : ∀ i, L.cbi i ∈ L.fns` using `fun i => by simp [LevelData.fns]`. Establish `h1 : L.Dr * L.Dri = 1` using `prod_mul_prod_eq_one r _ _ (fun i j => L.fns_comm _ (mc i) _ (mci j)) L.c_ci`.

Establish `h2 : L.Drbi * L.Drb = 1` using `prod_mul_prod_eq_one r _ _ (fun i j => L.fns_comm _ (mcbi i) _ (mcb j)) L.cbi_cb`. Establish `mDr : L.Dr ∈ Submonoid.closure L.fns` using `prod_mem L _ mc`. Establish `mζ : L.ζ ∈ Submonoid.closure L.fns` using `Submonoid.subset_closure (by simp [LevelData.fns])`. Establish `mζi : L.ζi ∈ Submonoid.closure L.fns` using `Submonoid.subset_closure (by simp [LevelData.fns])`. Establish `mζb : L.ζb ∈ Submonoid.closure L.fns` using `Submonoid.subset_closure (by simp [LevelData.fns])`.

Establish `mζbi : L.ζbi ∈ Submonoid.closure L.fns` using `Submonoid.subset_closure (by simp [LevelData.fns])`. Establish `mGGi : L.GGi ∈ Submonoid.closure L.fns` using `Submonoid.subset_closure (by simp [LevelData.fns])`. Establish `e1 : L.D * L.Dbi * (L.Drb * L.Dri) = L.ζ * L.ζbi`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [LevelData.D, LevelData.Dbi, mul_assoc]`.

Use `_ = L.ζ * L.ζbi := by`. Rewrite using `[h2, mul_one, (comm_of_closure L mDr (mul_mem mζ mζbi)).eq, mul_assoc, h1, mul_one]`. Rewrite using `[mul_assoc _ (L.D * L.Dbi), e1, (comm_of_closure L (mul_mem mζb mζi) mGGi).eq]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem phase (L : LevelData A r) : L.ζb * L.ζi * L.GGi * (L.D * L.Dbi) * (L.Drb * L.Dri) = L.GGi := by
  have mc : ∀ i, L.c i ∈ L.fns := fun i => by simp [LevelData.fns]
  have mci : ∀ i, L.ci i ∈ L.fns := fun i => by simp [LevelData.fns]
  have mcb : ∀ i, L.cb i ∈ L.fns := fun i => by simp [LevelData.fns]
  have mcbi : ∀ i, L.cbi i ∈ L.fns := fun i => by simp [LevelData.fns]
  have h1 : L.Dr * L.Dri = 1 :=
    prod_mul_prod_eq_one r _ _ (fun i j => L.fns_comm _ (mc i) _ (mci j)) L.c_ci
  have h2 : L.Drbi * L.Drb = 1 :=
    prod_mul_prod_eq_one r _ _ (fun i j => L.fns_comm _ (mcbi i) _ (mcb j)) L.cbi_cb
  have mDr : L.Dr ∈ Submonoid.closure L.fns := prod_mem L _ mc
  have mζ : L.ζ ∈ Submonoid.closure L.fns := Submonoid.subset_closure (by simp [LevelData.fns])
  have mζi : L.ζi ∈ Submonoid.closure L.fns := Submonoid.subset_closure (by simp [LevelData.fns])
  have mζb : L.ζb ∈ Submonoid.closure L.fns := Submonoid.subset_closure (by simp [LevelData.fns])
  have mζbi : L.ζbi ∈ Submonoid.closure L.fns := Submonoid.subset_closure (by simp [LevelData.fns])
  have mGGi : L.GGi ∈ Submonoid.closure L.fns := Submonoid.subset_closure (by simp [LevelData.fns])
  have e1 : L.D * L.Dbi * (L.Drb * L.Dri) = L.ζ * L.ζbi := by
    calc L.D * L.Dbi * (L.Drb * L.Dri) = L.Dr * (L.ζ * L.ζbi) * (L.Drbi * L.Drb) * L.Dri := by
          simp only [LevelData.D, LevelData.Dbi, mul_assoc]
      _ = L.ζ * L.ζbi := by
          rw [h2, mul_one, (comm_of_closure L mDr (mul_mem mζ mζbi)).eq, mul_assoc, h1, mul_one]
  rw [mul_assoc _ (L.D * L.Dbi), e1, (comm_of_closure L (mul_mem mζb mζi) mGGi).eq]
  calc L.GGi * (L.ζb * L.ζi) * (L.ζ * L.ζbi) = L.GGi * (L.ζb * (L.ζi * L.ζ) * L.ζbi) := by simp only [mul_assoc]
    _ = L.GGi := by rw [L.ζi_ζ, mul_one, L.ζb_ζbi, mul_one]

end GlobalTheory.HatNF.StartForm

namespace GlobalTheory.HatNF

open StartForm

open MeasureTheory in
/- English proof (translation)
The claim follows from `| 0, _, _, _, _ => by simp | n + 1, f, g, h, hc => by rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons] have hrest : (List.ofFn fun i : Fin n => f i.succ).prod * (List.ofFn fun i : Fin n => g i.succ).prod = 1 := prod_ofFn_mul_prod_ofFn_eq_one _ _ (fun i => h i.s …`.
-/
private lemma prod_ofFn_mul_prod_ofFn_eq_one {A : Type} [Ring A] :
    ∀ {n : ℕ} (f g : Fin n → A), (∀ i, f i * g i = 1) → (∀ i j, Commute (f i) (g j)) →
      (List.ofFn f).prod * (List.ofFn g).prod = 1
  | 0, _, _, _, _ => by simp
  | n + 1, f, g, h, hc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have hrest : (List.ofFn fun i : Fin n => f i.succ).prod *
        (List.ofFn fun i : Fin n => g i.succ).prod = 1 :=
      prod_ofFn_mul_prod_ofFn_eq_one _ _ (fun i => h i.succ) (fun i j => hc i.succ j.succ)
    have hcomm : Commute (List.ofFn fun i : Fin n => f i.succ).prod (g 0) := by
      refine Commute.list_prod_left _ _ ?_
      intro b hb
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
      exact hc i.succ 0
    calc f 0 * (List.ofFn fun i : Fin n => f i.succ).prod *
          (g 0 * (List.ofFn fun i : Fin n => g i.succ).prod)
        = f 0 * ((List.ofFn fun i : Fin n => f i.succ).prod * g 0) *
            (List.ofFn fun i : Fin n => g i.succ).prod := by simp only [mul_assoc]
      _ = f 0 * g 0 * ((List.ofFn fun i : Fin n => f i.succ).prod *
            (List.ofFn fun i : Fin n => g i.succ).prod) := by rw [hcomm.eq]; simp only [mul_assoc]
      _ = 1 := by rw [h 0, hrest, one_mul]

open MeasureTheory in
/- English proof (translation)
The claim follows from `L.fns_comm x hx y hy`.
-/
private lemma levelConstants_commute {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : _root_.Formalism.FourierDecayAlt.R.LevelData A r)
    {x y : A}
    (hx : x ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪
      {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi})
    (hy : y ∈ Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪
      {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi}) : Commute x y :=
  L.fns_comm x hx y hy

open MeasureTheory in
/- English proof (translation)
Use `Commute.list_prod_right _ _ ?_` and prove the remaining obligations. Introduce `b hb`. Take `⟨i, rfl⟩` from `List.mem_ofFn.mp hb`. Conclude with `h i`.
-/
private lemma commute_prod_ofFn {A : Type} [Ring A] {n : ℕ} (a : A) (f : Fin n → A)
    (h : ∀ i, Commute a (f i)) : Commute a (List.ofFn f).prod := by
  refine Commute.list_prod_right _ _ ?_
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  exact h i

open MeasureTheory in

/- English proof (translation)
Introduce `P A _ _ _ _ d hHyp L st s hTie`. Take `⟨hA, hSame, hs, hQ, hinv⟩` from `hTie`. Take `⟨-, -, hRel, -⟩` from `hHyp`. Take `⟨-, hκfns, -⟩` from `hRel`. Take `⟨-, -, -, -, -, -, -, hζi, hζb, -, hGG, hGGi, -⟩` from `hSame`.

Establish `hst` using `hA.start`. Apply the tactic sequence `have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num`. Establish `hκ : ∀ (f : _root_.Formalism.FourierDecayAlt.M.Ty P → ℂ) (g : A), g ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A) → Commute (d.κ f) g`. Introduce `f g hg`. Conclude with `hκfns f g (Or.inl (by unfold _root_.Formalism.FourierDecayAlt.R.LevelData.fns; exact Or.inr hg))`.

Establish `hx : ∀ Y, st.x Y = s • d.x Y`. Introduce `Y`. Establish `h11` using `congrFun (congrFun (hQ Y) 1) 1`. Rewrite `h11` using `[hst.tau Y, hGG]`. Simplify using `only [Matrix.smul_apply, _root_.Formalism.FourierDecayAlt.Q.NFData.QQ] at h11`.

Simplify using `at h11`. Combine the equalities or inequalities in the displayed calculation. Establish `hxinv : ∀ Y ∈ st.inv, d.x Y * d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) = 1 ∧ d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * d.x Y = 1`. Introduce `Y hY`. Rewrite `hY` using `[hinv]`.

Unfold `_root_.Formalism.FourierDecayAlt.Q.NFData.x`. Rewrite using `[← map_mul, ← map_mul, ← map_one d.κ]`. Prove the components needed by the constructor for the conclusion. Use `congr 1`. Use function extensionality and compare the values at `ρ`.

Conclude with `mul_inv_cancel₀ (hY ρ)`. Use `congr 1`. Use function extensionality and compare the values at `ρ`. Conclude with `inv_mul_cancel₀ (hY ρ)`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `a ha`. Establish `hle : _root_.Formalism.FourierDecayAlt.TL.kAlg st ≤ d.κ.range`. Unfold `_root_.Formalism.FourierDecayAlt.TL.kAlg`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `b (⟨Y, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)`.

Rewrite using `[hx Y]`. Unfold `_root_.Formalism.FourierDecayAlt.Q.NFData.x`. Conclude with `⟨s • fun ρ => _root_.Formalism.FourierDecayAlt.M.xC P ρ Y, by simp [map_smul]⟩`. Establish `hxi : st.xi Y = s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)`. Establish `hright : st.x Y * (s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) = 1`.

Rewrite using `[hx Y, smul_mul_smul_comm, mul_inv_cancel₀ hs0, (hxinv Y hY).1, one_smul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hright, mul_one]`. Use `_ = s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) := by`. Rewrite using `[← mul_assoc, (hst.x_xi Y hY).2, one_mul]`.

Rewrite using `[hxi]`. Conclude with `⟨s⁻¹ • fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹, by simp [map_smul]⟩`. Rewrite using `[← AlgHom.coe_range]`. Conclude with `hle ha`. Introduce `Y hY`.

Take `⟨hXXi, hXiX⟩` from `hxinv Y hY`. Establish `h10` using `congrFun (congrFun (hQ Y) 1) 0`. Rewrite `h10` using `[hst.low Y hY, hx Y, hGG, hζb, hζi, hGGi]`. Simplify using `only [Matrix.smul_apply, _root_.Formalism.FourierDecayAlt.Q.NFData.QQ] at h10`. Simplify using `at h10`.

Rewrite `h10` using `[← smul_add]`. Establish `h10' : d.L.GG * d.x Y * (L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * st.ee Y) = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y`. Establish `h` using `congrArg (fun a => s⁻¹ • a) h10`. Simplify `h` using `only [smul_smul, inv_mul_cancel₀ hs0, one_smul]`. Establish `hcancel : ∀ a : A, d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * (d.L.GG * d.x Y * a)) = a`.

Introduce `a`. Simplify using `only [← mul_assoc]`. Rewrite using `[mul_assoc _ d.L.GGi d.L.GG, d.L.GGi_GG, mul_one, hXiX, one_mul]`. Establish `key : L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * st.ee Y = d.L.l0 Y + d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * d.weightedSumBis Y)`. Establish `h : d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * (d.L.GG * d.x Y * (L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * st.ee Y))) = d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y))`.

Rewrite using `[h10']`. Rewrite `h` using `[hcancel, mul_add, mul_add, hcancel]`. Conclude with `h`. Establish `hmem : ∀ b ∈ _root_.GlobalTheory.HatNF.bmon d, b ∈ _root_.GlobalTheory.HatNF.nfSpan d ∅ 0 0 0`. Introduce `b hb`.

Unfold `_root_.GlobalTheory.HatNF.nfSpan`. Conclude with `Submodule.subset_span ⟨b, hb, [], rfl, by simp, by simp⟩`. Establish `hgen : ∀ b ∈ _root_.GlobalTheory.HatNF.bset d, b ∈ _root_.GlobalTheory.HatNF.bmon d`. Introduce `b hb`. Unfold `_root_.GlobalTheory.HatNF.bmon`.

Conclude with `Submonoid.subset_closure hb`. Establish `hκgen : ∀ f : _root_.Formalism.FourierDecayAlt.M.Ty P → ℂ, d.κ f ∈ _root_.GlobalTheory.HatNF.bmon d` using `fun f => hgen _ (by unfold _root_.GlobalTheory.HatNF.bset; exact Or.inl (Or.inl (Or.inr ⟨f, rfl⟩)))`. Establish `hDgen : d.L.D * d.L.Dbi ∈ _root_.GlobalTheory.HatNF.bmon d` using `hgen _ (by unfold _root_.GlobalTheory.HatNF.bset; exact Or.inl (Or.inl (Or.inl (by simp))))`. Establish `hPgen : ∀ l ∈ Finset.Icc 1 (P.k - 1), d.L.Drb * d.L.Dri * d.SS l ∈ _root_.GlobalTheory.HatNF.bmon d`. Introduce `l hl`.

Use `hgen _ ?_` and prove the remaining obligations. Unfold `_root_.GlobalTheory.HatNF.bset`. Use `Or.inl (Or.inr ⟨l, by simpa using hl, ?_⟩)` and prove the remaining obligations. Unfold `_root_.GlobalTheory.HatNF.ssn`. Both sides reduce to the same expression.

Establish `hDD : ∀ l, d.L.D * d.L.Dbi * (d.L.Drb * d.L.Dri * d.SS l) = d.L.ζ * (d.L.ζbi * d.SS l)`. Introduce `l`. Establish `hcb : (List.ofFn d.L.cbi).prod * (List.ofFn d.L.cb).prod = 1` using `prod_ofFn_mul_prod_ofFn_eq_one _ _ d.L.cbi_cb (fun i j => levelConstants_commute d.L (by simp) (by simp))`. Establish `hc : (List.ofFn d.L.c).prod * (List.ofFn d.L.ci).prod = 1` using `prod_ofFn_mul_prod_ofFn_eq_one _ _ d.L.c_ci (fun i j => levelConstants_commute d.L (by simp) (by simp))`. Establish `hζci : Commute d.L.ζ (List.ofFn d.L.ci).prod` using `commute_prod_ofFn _ _ (fun i => levelConstants_commute d.L (by simp) (by simp))`.

Establish `hζbici : Commute d.L.ζbi (List.ofFn d.L.ci).prod` using `commute_prod_ofFn _ _ (fun i => levelConstants_commute d.L (by simp) (by simp))`. Unfold `_root_.Formalism.FourierDecayAlt.R.LevelData.D _root_.Formalism.FourierDecayAlt.R.LevelData.Dbi _root_.Formalism.FourierDecayAlt.R.LevelData.Drb _root_.Formalism.FourierDecayAlt.R.LevelData.Dri _root_.Formalism.FourierDecayAlt.R.LevelData.Dr _root_.Formalism.FourierDecayAlt.R.Lev …`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc (List.ofFn d.L.cbi).prod, hcb, one_mul, ← hζbici.symm.left_comm, ← hζci.symm.left_comm, ← mul_assoc, hc, one_mul]`. Establish `hGGiζ : Commute d.L.GGi d.L.ζ` using `levelConstants_commute d.L (by simp) (by simp)`.

Establish `hGGiζbi : Commute d.L.GGi d.L.ζbi` using `levelConstants_commute d.L (by simp) (by simp)`. Establish `hXiζ : Commute (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) d.L.ζ` using `hκ _ _ (by simp)`. Establish `hXiζbi : Commute (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) d.L.ζbi` using `hκ _ _ (by simp)`. Establish `hXiGGi : Commute (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) d.L.GGi` using `hκ _ _ (by simp)`. Use `⟨d.L.ζ * (d.L.ζbi * (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * d.weightedSumBis Y)), ?_, ?_⟩` and prove the remaining obligations.

Establish `hS : d.weightedSumBis Y = ∑ l ∈ Finset.Icc 1 (P.k - 1), d.SS l * d.κ (fun ρ => _root_.Formalism.FourierDecayAlt.M.xEx P {l} ρ Y)` using `rfl`. Rewrite using `[hS, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]`. Use `Submodule.sum_mem _ (fun l hl => hmem _ ?_)` and prove the remaining obligations. Establish `heq : d.L.ζ * (d.L.ζbi * (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.SS l * d.κ (fun ρ => _root_.Formalism.FourierDecayAlt.M.xEx P {l} ρ Y)))) = d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.D * d.L.Dbi) * (d.L.Drb * d.L.Dri * d.SS …`. Rewrite using `[mul_assoc (d.κ _) (d.L.D * d.L.Dbi), hDD, ← hXiζbi.left_comm, ← hXiζ.left_comm]`.

Simplify using `only [mul_assoc]`. Rewrite using `[heq]`. Conclude with `mul_mem (mul_mem (mul_mem (hκgen _) hDgen) (hPgen l hl)) (hκgen _)`. Rewrite using `[hζb, hζi, hGGi, key]`. Use `congr 1`.

Simplify using `only [mul_assoc]`. Rewrite using `[hGGiζ.left_comm, hGGiζbi.left_comm, ← mul_assoc d.L.ζi, d.L.ζi_ζ, one_mul, ← mul_assoc d.L.ζb, d.L.ζb_ζbi, one_mul, hXiGGi.left_comm]`.
-/
theorem _root_.GlobalTheory.HatNF.start_normalForm : ∀ (P : _root_.Formalism.FourierDecayAlt.M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : _root_.Formalism.FourierDecayAlt.Q.NFData P A), _root_.GlobalTheory.HatNF.HatHyp d → ∀ (L : _root_.Formalism.FourierDecayAlt.R.LevelData A P.r) (st : _root_.Formalism.FourierDecayAlt.Fr.Start A) (s : ℂ), _root_.GlobalTheory.HatNF.Comparison₂ d L st s → (∀ x ∈ _root_.Formalism.FourierDecayAlt.TL.kAlg st, x ∈ Set.range d.κ) ∧ ∀ Y ∈ st.inv, ∃ E ∈ _root_.GlobalTheory.HatNF.nfSpan d ∅ 0 0 0, L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y = d.L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * E := by
  intro P A _ _ _ _ d hHyp L st s hTie
  obtain ⟨hA, hSame, hs, hQ, hinv⟩ := hTie
  obtain ⟨-, -, hRel, -⟩ := hHyp
  obtain ⟨-, hκfns, -⟩ := hRel
  obtain ⟨-, -, -, -, -, -, -, hζi, hζb, -, hGG, hGGi, -⟩ := hSame
  have hst := hA.start
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num

  have hκ : ∀ (f : _root_.Formalism.FourierDecayAlt.M.Ty P → ℂ) (g : A), g ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A) →
      Commute (d.κ f) g := by
    intro f g hg
    exact hκfns f g (Or.inl (by unfold _root_.Formalism.FourierDecayAlt.R.LevelData.fns; exact Or.inr hg))

  have hx : ∀ Y, st.x Y = s • d.x Y := by
    intro Y
    have h11 := congrFun (congrFun (hQ Y) 1) 1
    rw [hst.tau Y, hGG] at h11
    simp only [Matrix.smul_apply, _root_.Formalism.FourierDecayAlt.Q.NFData.QQ] at h11
    simp at h11
    calc st.x Y = d.L.GGi * (d.L.GG * st.x Y) := by rw [← mul_assoc, d.L.GGi_GG, one_mul]
      _ = s • d.x Y := by rw [h11, mul_smul_comm, ← mul_assoc, d.L.GGi_GG, one_mul]

  have hxinv : ∀ Y ∈ st.inv, d.x Y * d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) = 1 ∧
      d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * d.x Y = 1 := by
    intro Y hY
    rw [hinv] at hY
    unfold _root_.Formalism.FourierDecayAlt.Q.NFData.x
    rw [← map_mul, ← map_mul, ← map_one d.κ]
    constructor
    · congr 1; funext ρ; exact mul_inv_cancel₀ (hY ρ)
    · congr 1; funext ρ; exact inv_mul_cancel₀ (hY ρ)
  refine ⟨?_, ?_⟩
  · intro a ha
    have hle : _root_.Formalism.FourierDecayAlt.TL.kAlg st ≤ d.κ.range := by
      unfold _root_.Formalism.FourierDecayAlt.TL.kAlg
      refine Algebra.adjoin_le ?_
      rintro b (⟨Y, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
      · rw [hx Y]
        unfold _root_.Formalism.FourierDecayAlt.Q.NFData.x
        exact ⟨s • fun ρ => _root_.Formalism.FourierDecayAlt.M.xC P ρ Y, by simp [map_smul]⟩
      · have hxi : st.xi Y = s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) := by
          have hright : st.x Y * (s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) = 1 := by
            rw [hx Y, smul_mul_smul_comm, mul_inv_cancel₀ hs0, (hxinv Y hY).1, one_smul]
          calc st.xi Y = st.xi Y * (st.x Y * (s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹))) := by
                rw [hright, mul_one]
            _ = s⁻¹ • d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) := by
                rw [← mul_assoc, (hst.x_xi Y hY).2, one_mul]
        rw [hxi]
        exact ⟨s⁻¹ • fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹, by simp [map_smul]⟩
    rw [← AlgHom.coe_range]
    exact hle ha
  · intro Y hY
    obtain ⟨hXXi, hXiX⟩ := hxinv Y hY
    have h10 := congrFun (congrFun (hQ Y) 1) 0
    rw [hst.low Y hY, hx Y, hGG, hζb, hζi, hGGi] at h10
    simp only [Matrix.smul_apply, _root_.Formalism.FourierDecayAlt.Q.NFData.QQ] at h10
    simp at h10
    rw [← smul_add] at h10
    have h10' : d.L.GG * d.x Y * (L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * st.ee Y) =
        d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := by
      have h := congrArg (fun a => s⁻¹ • a) h10
      simpa only [smul_smul, inv_mul_cancel₀ hs0, one_smul] using h
    have hcancel : ∀ a : A, d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * (d.L.GG * d.x Y * a)) = a := by
      intro a
      simp only [← mul_assoc]
      rw [mul_assoc _ d.L.GGi d.L.GG, d.L.GGi_GG, mul_one, hXiX, one_mul]
    have key : L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * st.ee Y =
        d.L.l0 Y + d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * d.weightedSumBis Y) := by
      have h : d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * (d.L.GG * d.x Y *
          (L.l0 Y + d.L.ζb * d.L.ζi * d.L.GGi * st.ee Y))) =
          d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.GGi * (d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y)) := by
        rw [h10']
      rw [hcancel, mul_add, mul_add, hcancel] at h
      exact h
    have hmem : ∀ b ∈ _root_.GlobalTheory.HatNF.bmon d, b ∈ _root_.GlobalTheory.HatNF.nfSpan d ∅ 0 0 0 := by
      intro b hb
      unfold _root_.GlobalTheory.HatNF.nfSpan
      exact Submodule.subset_span ⟨b, hb, [], rfl, by simp, by simp⟩
    have hgen : ∀ b ∈ _root_.GlobalTheory.HatNF.bset d, b ∈ _root_.GlobalTheory.HatNF.bmon d := by
      intro b hb
      unfold _root_.GlobalTheory.HatNF.bmon
      exact Submonoid.subset_closure hb
    have hκgen : ∀ f : _root_.Formalism.FourierDecayAlt.M.Ty P → ℂ, d.κ f ∈ _root_.GlobalTheory.HatNF.bmon d := fun f =>
      hgen _ (by unfold _root_.GlobalTheory.HatNF.bset; exact Or.inl (Or.inl (Or.inr ⟨f, rfl⟩)))
    have hDgen : d.L.D * d.L.Dbi ∈ _root_.GlobalTheory.HatNF.bmon d :=
      hgen _ (by unfold _root_.GlobalTheory.HatNF.bset; exact Or.inl (Or.inl (Or.inl (by simp))))
    have hPgen : ∀ l ∈ Finset.Icc 1 (P.k - 1), d.L.Drb * d.L.Dri * d.SS l ∈ _root_.GlobalTheory.HatNF.bmon d := by
      intro l hl
      refine hgen _ ?_
      unfold _root_.GlobalTheory.HatNF.bset
      refine Or.inl (Or.inr ⟨l, by simpa using hl, ?_⟩)
      unfold _root_.GlobalTheory.HatNF.ssn
      rfl
    have hDD : ∀ l, d.L.D * d.L.Dbi * (d.L.Drb * d.L.Dri * d.SS l) = d.L.ζ * (d.L.ζbi * d.SS l) := by
      intro l
      have hcb : (List.ofFn d.L.cbi).prod * (List.ofFn d.L.cb).prod = 1 :=
        prod_ofFn_mul_prod_ofFn_eq_one _ _ d.L.cbi_cb
          (fun i j => levelConstants_commute d.L (by simp) (by simp))
      have hc : (List.ofFn d.L.c).prod * (List.ofFn d.L.ci).prod = 1 :=
        prod_ofFn_mul_prod_ofFn_eq_one _ _ d.L.c_ci
          (fun i j => levelConstants_commute d.L (by simp) (by simp))
      have hζci : Commute d.L.ζ (List.ofFn d.L.ci).prod :=
        commute_prod_ofFn _ _ (fun i => levelConstants_commute d.L (by simp) (by simp))
      have hζbici : Commute d.L.ζbi (List.ofFn d.L.ci).prod :=
        commute_prod_ofFn _ _ (fun i => levelConstants_commute d.L (by simp) (by simp))
      unfold _root_.Formalism.FourierDecayAlt.R.LevelData.D _root_.Formalism.FourierDecayAlt.R.LevelData.Dbi _root_.Formalism.FourierDecayAlt.R.LevelData.Drb _root_.Formalism.FourierDecayAlt.R.LevelData.Dri _root_.Formalism.FourierDecayAlt.R.LevelData.Dr _root_.Formalism.FourierDecayAlt.R.LevelData.Drbi
      simp only [mul_assoc]
      rw [← mul_assoc (List.ofFn d.L.cbi).prod, hcb, one_mul, ← hζbici.symm.left_comm,
        ← hζci.symm.left_comm, ← mul_assoc, hc, one_mul]
    have hGGiζ : Commute d.L.GGi d.L.ζ := levelConstants_commute d.L (by simp) (by simp)
    have hGGiζbi : Commute d.L.GGi d.L.ζbi := levelConstants_commute d.L (by simp) (by simp)
    have hXiζ : Commute (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) d.L.ζ := hκ _ _ (by simp)
    have hXiζbi : Commute (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) d.L.ζbi := hκ _ _ (by simp)
    have hXiGGi : Commute (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹)) d.L.GGi := hκ _ _ (by simp)
    refine ⟨d.L.ζ * (d.L.ζbi * (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * d.weightedSumBis Y)), ?_, ?_⟩
    · have hS : d.weightedSumBis Y = ∑ l ∈ Finset.Icc 1 (P.k - 1), d.SS l * d.κ (fun ρ => _root_.Formalism.FourierDecayAlt.M.xEx P {l} ρ Y) := rfl
      rw [hS, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Submodule.sum_mem _ (fun l hl => hmem _ ?_)
      have heq : d.L.ζ * (d.L.ζbi * (d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) *
          (d.SS l * d.κ (fun ρ => _root_.Formalism.FourierDecayAlt.M.xEx P {l} ρ Y)))) =
          d.κ (fun ρ => (_root_.Formalism.FourierDecayAlt.M.xC P ρ Y)⁻¹) * (d.L.D * d.L.Dbi) * (d.L.Drb * d.L.Dri * d.SS l) *
            d.κ (fun ρ => _root_.Formalism.FourierDecayAlt.M.xEx P {l} ρ Y) := by
        rw [mul_assoc (d.κ _) (d.L.D * d.L.Dbi), hDD, ← hXiζbi.left_comm, ← hXiζ.left_comm]
        simp only [mul_assoc]
      rw [heq]
      exact mul_mem (mul_mem (mul_mem (hκgen _) hDgen) (hPgen l hl)) (hκgen _)
    · rw [hζb, hζi, hGGi, key]
      congr 1
      simp only [mul_assoc]
      rw [hGGiζ.left_comm, hGGiζbi.left_comm, ← mul_assoc d.L.ζi, d.L.ζi_ζ, one_mul,
        ← mul_assoc d.L.ζb, d.L.ζb_ζbi, one_mul, hXiGGi.left_comm]

end GlobalTheory.HatNF
