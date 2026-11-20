import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsExpSmulA
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ZpowNeOneOfClose

noncomputable section
open Classical

namespace GlobalTheory.LevelClauseOdd

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

/- English proof (translation)
Establish `: Algebra.IsAlgebraic ↥(K0 K) (Om l)` using `Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _`. Take `⟨σ, hσ⟩` from `IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ_[l]) (L := ↥(K0 K)) (M := Om l) (E := Om l) ((LL.1.val).comp (((HW l).W K 1 LL hA.2.2).emb c))`. Establish `hσx : ∀ x : ↥(K0 K), σ (x : Om l) = ((((HW l).W K 1 LL hA.2.2).emb c x : ↥LL.1) : Om l)` using `fun x => by`. Use `congrArg (fun f => f x) hσ` as an intermediate fact. Simplify `this` using `[AlgHom.domRestrict]`.

Establish `hζ₁` using `Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l`. Establish `hσinj : Function.Injective σ` using `σ.toRingHom.injective`. Establish `hζO : IsPrimitiveRoot ((ζ : ↥LL.1) : Om l) l` using `hζ.map_of_injective (f := LL.1.val) Subtype.val_injective`. Establish `hσζ₁ : IsPrimitiveRoot (σ ((D.loc l).ζQ 1)) l` using `hζ₁.map_of_injective hσinj`. Establish `: NeZero l` using `⟨(Fact.out : l.Prime).ne_zero⟩`.

Take `⟨b, -, hb⟩` from `hσζ₁.eq_pow_of_pow_eq_one hζO.pow_eq_one`. Establish `hβ : IsPrimitiveRoot ((D.loc l).ζQ 1 ^ b) l`. Apply `IsPrimitiveRoot.of_map_of_injective (f := σ) _ hσinj` to reduce the goal to its premises. Rewrite using `[map_pow, hb]`. Conclude with `hζO`.

Take `⟨g, hg⟩` from `Formalism.MainNotions.UnusedSlot80.LevR.trans_prim (D.loc l) ((HW l).W K 1 LL hA.2.2) (Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F h9 l K LL hA) hζ₁ _ hβ`. Establish `hmem : ∀ y, ((σ.comp (g : GQ l).toAlgHom).comp (Ks K 1).val) y ∈ LL.1` using `hA.2.2.2.2.2 _`. Set `τs : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1` to `((σ.comp (g : GQ l).toAlgHom).comp (Ks K 1).val).codRestrict LL.1.toSubalgebra hmem`. Use `⟨τs.comp (IntermediateField.inclusion hA.2.2.2.2.1), τs, ⟨fun x y hxy => ?_, fun y hy => ?_⟩, fun x y hxy => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext show σ ((g : GQ l) (y : Om l)) = _` to reduce the goal to its premises.

Establish `hgx : (g : GQ l) (x : Om l) = x` using `(IntermediateField.mem_fixingSubgroup_iff K.1 (g : GQ l)).mp g.2 _ ((inf_le_left : K0 K ≤ K.1) x.2)`. Rewrite using `[hxy, hgx, hσx]`. Apply `Subtype.ext show σ ((g : GQ l) (y : Om l)) = _` to reduce the goal to its premises. Rewrite using `[hy, hg, map_pow, hb]`. Use `show τs _ = τs y`.

Use `congr 1`. Conclude with `Subtype.ext hxy.symm`.
-/
theorem exists_point_over_letter (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL)
    (c : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ l) :
    ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hA.2.2 c ζ τ := by
  have : Algebra.IsAlgebraic ↥(K0 K) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
  obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ_[l]) (L := ↥(K0 K))
    (M := Om l) (E := Om l) ((LL.1.val).comp (((HW l).W K 1 LL hA.2.2).emb c))
  have hσx : ∀ x : ↥(K0 K),
      σ (x : Om l) = ((((HW l).W K 1 LL hA.2.2).emb c x : ↥LL.1) : Om l) := fun x => by
    have := congrArg (fun f => f x) hσ
    simpa [AlgHom.domRestrict] using this
  have hζ₁ := Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l
  have hσinj : Function.Injective σ := σ.toRingHom.injective
  have hζO : IsPrimitiveRoot ((ζ : ↥LL.1) : Om l) l :=
    hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  have hσζ₁ : IsPrimitiveRoot (σ ((D.loc l).ζQ 1)) l := hζ₁.map_of_injective hσinj
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨b, -, hb⟩ := hσζ₁.eq_pow_of_pow_eq_one hζO.pow_eq_one
  have hβ : IsPrimitiveRoot ((D.loc l).ζQ 1 ^ b) l := by
    apply IsPrimitiveRoot.of_map_of_injective (f := σ) _ hσinj
    rw [map_pow, hb]
    exact hζO
  obtain ⟨g, hg⟩ := Formalism.MainNotions.UnusedSlot80.LevR.trans_prim (D.loc l) ((HW l).W K 1 LL hA.2.2)
    (Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F h9 l K LL hA) hζ₁ _ hβ
  have hmem : ∀ y, ((σ.comp (g : GQ l).toAlgHom).comp (Ks K 1).val) y ∈ LL.1 :=
    hA.2.2.2.2.2 _
  let τs : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1 :=
    ((σ.comp (g : GQ l).toAlgHom).comp (Ks K 1).val).codRestrict LL.1.toSubalgebra hmem
  refine ⟨τs.comp (IntermediateField.inclusion hA.2.2.2.2.1), τs,
    ⟨fun x y hxy => ?_, fun y hy => ?_⟩, fun x y hxy => ?_⟩
  · apply Subtype.ext
    show σ ((g : GQ l) (y : Om l)) = _
    have hgx : (g : GQ l) (x : Om l) = x :=
      (IntermediateField.mem_fixingSubgroup_iff K.1 (g : GQ l)).mp g.2 _
        ((inf_le_left : K0 K ≤ K.1) x.2)
    rw [hxy, hgx, hσx]
  · apply Subtype.ext
    show σ ((g : GQ l) (y : Om l)) = _
    rw [hy, hg, map_pow, hb]
  · show τs _ = τs y
    congr 1
    exact Subtype.ext hxy.symm

/- English proof (translation)
Establish `tie` using `((Cm l).C K 1 LL hA.2.2).tie`. Establish `hs` using `(HW l).W_s K 1 LL hA.2.2`. Establish `hp : ((((D.loc l).PD K).p : ℕ) : ↥LL.1) ≠ 0`. Introduce `h`. Establish `hv` using `((HW l).W K 1 LL hA.2.2).v_l`.

Rewrite `hv` using `[h, AddValuation.map_zero]`. Conclude with `WithTop.top_ne_one hv`. Establish `hsurj : Function.Surjective (algebraMap ↥(K0 K) ↥K.1)` using `fun x => ⟨⟨x, x.2, hA.1 x.2⟩, rfl⟩`. Use `Formalism.MainNotions.UnusedSlot80.LevR.level_condition_of_level_zero _ ((Cm l).C K 1 LL hA.2.2).tie.levB hs ((Cm l).C K 1 LL hA.2.2).tie.levN_eq ((Cm l).C K 1 LL hA.2.2).tie.levB_φ hp ?_` and prove the remaining obligations. Introduce `T hT c ζ hζ`.

Establish `hζl : IsPrimitiveRoot ζ l` using `by rwa [(D.loc l).PD_p] at hζ`. Take `⟨τ, hτ⟩` from `exists_point_over_letter D HW F h9 l K LL hA c ζ hζl`. Establish `hover : ∀ x : ↥(K0 K), τ (algebraMap ↥(K0 K) ↥K.1 x) = ((HW l).W K 1 LL hA.2.2).emb c x`. Take `⟨τs, ⟨hemb, -⟩, hres⟩` from `hτ`. Introduce `x`.

Establish `hy : (x : Om l) ∈ Ks K 1` using `(le_sup_left : K0 K ≤ Ks K 1) x.2`. Rewrite using `[hres (algebraMap ↥(K0 K) ↥K.1 x) ⟨x, hy⟩ rfl]`. Conclude with `hemb x ⟨x, hy⟩ rfl`. Establish `h4'` using `((h4 l K 1 LL hA.2.2 T hT).2 c ζ τ hτ).2`. Conclude with `Formalism.MainNotions.UnusedSlot80.LevR.lev0 _ T c ζ τ (Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le _ T c τ hover hsurj) h4'`.
-/
theorem clause_at_levels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL) :
    Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL hA.2.2) := by
  have tie := ((Cm l).C K 1 LL hA.2.2).tie
  have hs := (HW l).W_s K 1 LL hA.2.2
  have hp : ((((D.loc l).PD K).p : ℕ) : ↥LL.1) ≠ 0 := by
    intro h
    have hv := ((HW l).W K 1 LL hA.2.2).v_l
    rw [h, AddValuation.map_zero] at hv
    exact WithTop.top_ne_one hv
  have hsurj : Function.Surjective (algebraMap ↥(K0 K) ↥K.1) :=
    fun x => ⟨⟨x, x.2, hA.1 x.2⟩, rfl⟩
  refine Formalism.MainNotions.UnusedSlot80.LevR.level_condition_of_level_zero _ ((Cm l).C K 1 LL hA.2.2).tie.levB hs
    ((Cm l).C K 1 LL hA.2.2).tie.levN_eq ((Cm l).C K 1 LL hA.2.2).tie.levB_φ hp ?_
  intro T hT c ζ hζ
  have hζl : IsPrimitiveRoot ζ l := by rwa [(D.loc l).PD_p] at hζ
  obtain ⟨τ, hτ⟩ := exists_point_over_letter D HW F h9 l K LL hA c ζ hζl
  have hover : ∀ x : ↥(K0 K), τ (algebraMap ↥(K0 K) ↥K.1 x) = ((HW l).W K 1 LL hA.2.2).emb c x := by
    obtain ⟨τs, ⟨hemb, -⟩, hres⟩ := hτ
    intro x
    have hy : (x : Om l) ∈ Ks K 1 := (le_sup_left : K0 K ≤ Ks K 1) x.2
    rw [hres (algebraMap ↥(K0 K) ↥K.1 x) ⟨x, hy⟩ rfl]
    exact hemb x ⟨x, hy⟩ rfl
  have h4' := ((h4 l K 1 LL hA.2.2 T hT).2 c ζ τ hτ).2
  exact Formalism.MainNotions.UnusedSlot80.LevR.lev0 _ T c ζ τ (Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le _ T c τ hover hsurj) h4'

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `hl3' : 3 ≤ l`. Establish `h2` using `(Fact.out : l.Prime).two_le`. Establish `hodd : l ≠ 2` using `hA.2.1`. Use linear arithmetic over natural numbers and integers. Use `set W := (HW l).W K 1 LL hA.2.2 with hW`.

Introduce `ζ ζ' hζ hζ'`. Establish `hpl : ((D.loc l).PD K).p = l` using `(D.loc l).PD_p K`. Rewrite `hζ`, `hζ'` using `[hpl]`. Establish `hcard` using `Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F h9 l K LL hA`. Establish `hv : (D.loc l).v LL ((l : ℕ) : ↥LL.1) = 1` using `(D.loc l).v_l LL`.

Establish `hvO` using `(D.loc l).v_O LL`. Establish `hl0 : ((l : ℕ) : ↥LL.1) ≠ 0`. Introduce `h`. Rewrite `hv` using `[h, AddValuation.map_zero]`. Conclude with `WithTop.top_ne_coe hv`.

Establish `hcong : ∀ δ : ↥W.DelF, ∃ a : ℕ, ((1 : ℕ) : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ : ↥(OL LL)) - (a : ↥LL.1))`. Introduce `δ`. Take `⟨g, hg⟩` from `W.resΓ_onto δ`. Take `⟨a, ha, -⟩` from `(D.loc l).χQ_cyc (g : GQ l) 1 ((D.loc l).ζQ 1) (by rw [pow_one]; exact (Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l).pow_eq_one)`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Establish `hres` using `W.χΓ_res g`. Establish `hPD` using `(D.loc l).PD_χ K g`. Rewrite using `[← hg, hres, hPD]`. Use `set t : ℚ_[l] := ((D.loc l).χQ (g : GQ l) : ℚ_[l]) - (a : ℚ_[l]) with ht`. Establish `hlQ : ((l : ℕ) : ℚ_[l]) ≠ 0` using `by exact_mod_cast (Fact.out : l.Prime).ne_zero`.

Establish `e : algebraMap ℚ_[l] ↥LL.1 ((D.loc l).χQ (g : GQ l) : ℚ_[l]) - (a : ↥LL.1) = ((l : ℕ) : ↥LL.1) * algebraMap ℚ_[l] ↥LL.1 (t / (l : ℚ_[l]))`. Rewrite using `[map_div₀, map_natCast, mul_div_cancel₀ _ hl0, ht, map_sub, map_natCast]`. Rewrite using `[e, AddValuation.map_mul, hv]`. Establish `hz : ‖t / (l : ℚ_[l])‖ ≤ 1`. Rewrite using `[norm_div, Padic.norm_p, div_le_one (by first`.

Consider the case `positivity`. Consider the case `exact inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos))]`. Use `ha` as an intermediate fact. Simplify `this` using `[zpow_neg, zpow_one]`. Establish `hint : algebraMap ℚ_[l] ↥LL.1 (t / (l : ℚ_[l])) ∈ OL LL`.

Establish `e2 : algebraMap ℚ_[l] ↥LL.1 (t / (l : ℚ_[l])) = algebraMap ℤ_[l] ↥LL.1 (⟨t / (l : ℚ_[l]), hz⟩ : ℤ_[l])` using `(IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1 (⟨t / (l : ℚ_[l]), hz⟩ : ℤ_[l])).symm`. Rewrite using `[e2]`. Conclude with `(algebraMap ℤ_[l] ↥(OL LL) (⟨t / (l : ℚ_[l]), hz⟩ : ℤ_[l])).2`. Conclude with `le_add_of_nonneg_right ((hvO _).2 hint)`. Use `choose aδ haδ using hcong`.

Establish `hvunit : ∀ w : (↥(OL LL))ˣ, (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) = 0`. Introduce `w`. Establish `h1` using `(hvO (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)))).2 (w : ↥(OL LL)).2`. Establish `h2` using `(hvO (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)))).2 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)).2`. Establish `h3 : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) + (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL))) = 0`.

Rewrite using `[← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]`. Conclude with `le_antisymm (le_trans (le_add_of_nonneg_right h2) h3.le) h1`. Establish `hne : ∀ δ, ((aδ δ : ℕ) : ZMod l) ≠ 0`. Introduce `δ h`. Rewrite `h` using `[ZMod.natCast_eq_zero_iff]`.

Take `⟨c, hc⟩` from `h`. Establish `hva : (1 : WithTop ℚ) ≤ (D.loc l).v LL ((aδ δ : ℕ) : ↥LL.1)`. Rewrite using `[hc, Nat.cast_mul, AddValuation.map_mul, hv]`. Conclude with `le_add_of_nonneg_right (Formalism.MainNotions.N.Pv.LocalLengthBound.Val.v_natCast_nonneg _ c)`. Establish `hsum` using `AddValuation.map_add ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ : ↥(OL LL)) - (aδ δ : ↥LL.1)) ((aδ δ : ℕ) : ↥LL.1)`.

Rewrite `hsum` using `[sub_add_cancel, hvunit]`. Establish `h1` using `haδ δ`. Rewrite `h1` using `[Nat.cast_one]`. Conclude with `absurd hsum (not_le.2 (lt_of_lt_of_le (by exact_mod_cast zero_lt_one) (le_min h1 hva)))`. Set `U : ↥W.DelF → (ZMod l)ˣ` to `fun δ => Units.mk0 _ (hne δ)`.

Establish `hUinj : Function.Injective U`. Introduce `δ δ' h`. Establish `h1 : ((aδ δ : ℕ) : ZMod l) = ((aδ δ' : ℕ) : ZMod l)` using `congrArg Units.val h`. Rewrite `h1` using `[ZMod.natCast_eq_natCast_iff']`. Use `set χd := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ : ↥(OL LL))`.

Use `set χd' := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ' : ↥(OL LL))`. Establish `hdiff : (1 : WithTop ℚ) ≤ (D.loc l).v LL (χd - χd')`. Establish `e : χd - χd' = (χd - (aδ δ : ↥LL.1)) - (χd' - (aδ δ' : ↥LL.1)) + ((aδ δ : ↥LL.1) - (aδ δ' : ↥LL.1))` using `by ring`. Rewrite using `[e]`. Establish `hA1` using `haδ δ`.

Establish `hA2` using `haδ δ'`. Rewrite `hA1`, `hA2` using `[Nat.cast_one]`. Use `le_trans (le_min (le_trans (le_min hA1 hA2) (AddValuation.map_sub ((D.loc l).v LL) _ _)) ?_) (AddValuation.map_add ((D.loc l).v LL) _ _)` and prove the remaining obligations. Break down `le_total (aδ δ') (aδ δ) with hle | hle` into its components or cases. Establish `hd : l ∣ aδ δ - aδ δ'` using `(Nat.modEq_iff_dvd' hle).1 h1.symm`.

Take `⟨c, hc⟩` from `hd`. Establish `e2 : ((aδ δ : ℕ) : ↥LL.1) - ((aδ δ' : ℕ) : ↥LL.1) = ((aδ δ - aδ δ' : ℕ) : ↥LL.1)`. Rewrite using `[Nat.cast_sub hle]`. Rewrite using `[e2, hc, Nat.cast_mul, AddValuation.map_mul, hv]`. Conclude with `le_add_of_nonneg_right (Formalism.MainNotions.N.Pv.LocalLengthBound.Val.v_natCast_nonneg _ c)`.

Establish `hd : l ∣ aδ δ' - aδ δ` using `(Nat.modEq_iff_dvd' hle).1 h1`. Take `⟨c, hc⟩` from `hd`. Establish `e2 : ((aδ δ : ℕ) : ↥LL.1) - ((aδ δ' : ℕ) : ↥LL.1) = -((aδ δ' - aδ δ : ℕ) : ↥LL.1)`. Rewrite using `[Nat.cast_sub hle]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e2, AddValuation.map_neg, hc, Nat.cast_mul, AddValuation.map_mul, hv]`. Conclude with `le_add_of_nonneg_right (Formalism.MainNotions.N.Pv.LocalLengthBound.Val.v_natCast_nonneg _ c)`. Use `set g := (δ : W.Gam) * (δ' : W.Gam)⁻¹`. Establish `hξ : algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) = χd * χd'⁻¹`. Establish `hχ'0 : χd' ≠ 0`.

Introduce `h0`. Use `hvunit (W.χΓ δ')` as an intermediate fact. Express the relevant statement in the definitionally equal form `(D.loc l).v LL χd' = 0 at this`. Rewrite `this` using `[h0, AddValuation.map_zero]`. Conclude with `WithTop.top_ne_coe this`.

Rewrite using `[eq_mul_inv_iff_mul_eq₀ hχ'0]`. Simplify using `only [χd, χd', g, ← map_mul, ← Units.val_mul, ← map_mul (W.χΓ), inv_mul_cancel_right]`. Establish `hξ1 : (1 : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) - 1)`. Establish `hχ'0 : χd' ≠ 0`. Introduce `h0`.

Use `hvunit (W.χΓ δ')` as an intermediate fact. Express the relevant statement in the definitionally equal form `(D.loc l).v LL χd' = 0 at this`. Rewrite `this` using `[h0, AddValuation.map_zero]`. Conclude with `WithTop.top_ne_coe this`. Establish `e : χd * χd'⁻¹ - 1 = (χd - χd') * χd'⁻¹` using `by field_simp`.

Rewrite using `[hξ, e, AddValuation.map_mul]`. Establish `hinv : (D.loc l).v LL χd'⁻¹ = 0`. Use `hvunit (W.χΓ δ')⁻¹` as an intermediate fact. Simplify `this` using `[χd', map_inv₀]`. Rewrite using `[hinv, add_zero]`.

Conclude with `hdiff`. Take `⟨k, hk, hδk⟩` from `(W.DelF_def δ).1 δ.2`. Take `⟨k', hk', hδk'⟩` from `(W.DelF_def δ').1 δ'.2`. Establish `hgk : g ^ (k * k') = 1`. Simplify using `only [g, mul_pow, inv_pow]`.

Rewrite using `[pow_mul, hδk, one_pow, one_mul, mul_comm k k', pow_mul, hδk', one_pow, inv_one]`. Establish `hξk : (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL))) ^ (k * k') = 1`. Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, hgk, map_one, Units.val_one, map_one]`. Establish `hl3 : 3 ≤ l`. Establish `h2` using `(Fact.out : l.Prime).two_le`.

Establish `hodd : l ≠ 2` using `hA.2.1`. Use linear arithmetic over natural numbers and integers. Establish `hξeq : algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) = 1`. Assume the negation of the conclusion as `hne1`. Conclude with `Formalism.MainNotions.N.Pv.LocalLengthBound.Val.pow_ne_one_of_close ((D.loc l).v LL) (Fact.out : l.Prime) hv hl3 (k * k') _ (Nat.mul_pos hk hk') hξ1 hne1 hξk`.

Establish `hg1 : g = 1`. Apply `W.χΓ_inj` to reduce the goal to its premises. Rewrite using `[map_one]`. Apply `Units.ext` to reduce the goal to its premises. Apply `Subtype.val_injective` to reduce the goal to its premises.

Simplify using `using hξeq`. Conclude with `Subtype.ext (mul_inv_eq_one.1 hg1)`. Establish `hUbij : Function.Bijective U`. Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Conclude with `⟨hUinj, by rw [Fintype.card_coe, hcard, ZMod.card_units]⟩`.

Take `⟨b, hb, hζb⟩` from `hζ.eq_pow_of_pow_eq_one hζ'.pow_eq_one`. Establish `hb0 : ((b : ℕ) : ZMod l) ≠ 0`. Rewrite using `[Ne, ZMod.natCast_eq_zero_iff]`. Introduce `hd`. Establish `: b = 0` using `Nat.eq_zero_of_dvd_of_lt hd hb`.

Substitute `this` using the available equality. Rewrite `hζb` using `[pow_zero]`. Conclude with `hζ'.ne_one (Fact.out : l.Prime).one_lt hζb.symm`. Take `⟨δ, hδ⟩` from `hUbij.2 (Units.mk0 _ hb0)`. Establish `h1 : ((aδ δ : ℕ) : ZMod l) = ((b : ℕ) : ZMod l)` using `congrArg Units.val hδ`.

Rewrite `h1` using `[ZMod.natCast_eq_natCast_iff]`. Establish `hpowmod : ∀ m : ℕ, ζ ^ m = ζ ^ (m % l)` using `fun m => by conv_lhs => rw [← Nat.mod_add_div m l, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]`. Use `⟨δ, δ.2, aδ δ, ?_, haδ δ⟩` and prove the remaining obligations. Rewrite using `[hpowmod, h1, ← hpowmod, hζb]`.
-/
theorem torsion_transitive (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL) :
    Formalism.MainNotions.N.Pv.LocalLengthBound.PtTrans ((HW l).W K 1 LL hA.2.2) := by
  have hl3' : 3 ≤ l := by
    have h2 := (Fact.out : l.Prime).two_le
    have hodd : l ≠ 2 := hA.2.1
    omega
  set W := (HW l).W K 1 LL hA.2.2 with hW
  intro ζ ζ' hζ hζ'
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  rw [hpl] at hζ hζ'
  have hcard := Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F h9 l K LL hA
  have hv : (D.loc l).v LL ((l : ℕ) : ↥LL.1) = 1 := (D.loc l).v_l LL
  have hvO := (D.loc l).v_O LL
  have hl0 : ((l : ℕ) : ↥LL.1) ≠ 0 := by
    intro h; rw [h, AddValuation.map_zero] at hv; exact WithTop.top_ne_coe hv

  have hcong : ∀ δ : ↥W.DelF, ∃ a : ℕ,
      ((1 : ℕ) : WithTop ℚ) ≤ (D.loc l).v LL
        (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ : ↥(OL LL)) - (a : ↥LL.1)) := by
    intro δ
    obtain ⟨g, hg⟩ := W.resΓ_onto δ
    obtain ⟨a, ha, -⟩ := (D.loc l).χQ_cyc (g : GQ l) 1 ((D.loc l).ζQ 1)
      (by rw [pow_one]; exact (Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l).pow_eq_one)
    refine ⟨a, ?_⟩
    have hres := W.χΓ_res g
    have hPD := (D.loc l).PD_χ K g
    rw [← hg, hres, hPD]
    set t : ℚ_[l] := ((D.loc l).χQ (g : GQ l) : ℚ_[l]) - (a : ℚ_[l]) with ht
    have hlQ : ((l : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    have e : algebraMap ℚ_[l] ↥LL.1 ((D.loc l).χQ (g : GQ l) : ℚ_[l]) - (a : ↥LL.1) =
        ((l : ℕ) : ↥LL.1) * algebraMap ℚ_[l] ↥LL.1 (t / (l : ℚ_[l])) := by
      rw [map_div₀, map_natCast, mul_div_cancel₀ _ hl0, ht, map_sub, map_natCast]
    rw [e, AddValuation.map_mul, hv]
    have hz : ‖t / (l : ℚ_[l])‖ ≤ 1 := by
      rw [norm_div, Padic.norm_p, div_le_one (by
        first
          | positivity
          | exact inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos))]
      have := ha
      simpa [zpow_neg, zpow_one] using this
    have hint : algebraMap ℚ_[l] ↥LL.1 (t / (l : ℚ_[l])) ∈ OL LL := by
      have e2 : algebraMap ℚ_[l] ↥LL.1 (t / (l : ℚ_[l])) =
          algebraMap ℤ_[l] ↥LL.1 (⟨t / (l : ℚ_[l]), hz⟩ : ℤ_[l]) :=
        (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1 (⟨t / (l : ℚ_[l]), hz⟩ : ℤ_[l])).symm
      rw [e2]
      exact (algebraMap ℤ_[l] ↥(OL LL) (⟨t / (l : ℚ_[l]), hz⟩ : ℤ_[l])).2
    exact le_add_of_nonneg_right ((hvO _).2 hint)
  choose aδ haδ using hcong

  have hvunit : ∀ w : (↥(OL LL))ˣ, (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) = 0 := by
    intro w
    have h1 := (hvO (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)))).2 (w : ↥(OL LL)).2
    have h2 := (hvO (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)))).2
      ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)).2
    have h3 : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) +
        (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL))) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
    exact le_antisymm (le_trans (le_add_of_nonneg_right h2) h3.le) h1
  have hne : ∀ δ, ((aδ δ : ℕ) : ZMod l) ≠ 0 := by
    intro δ h
    rw [ZMod.natCast_eq_zero_iff] at h
    obtain ⟨c, hc⟩ := h
    have hva : (1 : WithTop ℚ) ≤ (D.loc l).v LL ((aδ δ : ℕ) : ↥LL.1) := by
      rw [hc, Nat.cast_mul, AddValuation.map_mul, hv]
      exact le_add_of_nonneg_right (Formalism.MainNotions.N.Pv.LocalLengthBound.Val.v_natCast_nonneg _ c)
    have hsum := AddValuation.map_add ((D.loc l).v LL)
      (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ : ↥(OL LL)) - (aδ δ : ↥LL.1))
      ((aδ δ : ℕ) : ↥LL.1)
    rw [sub_add_cancel, hvunit] at hsum
    have h1 := haδ δ
    rw [Nat.cast_one] at h1
    exact absurd hsum (not_le.2 (lt_of_lt_of_le (by exact_mod_cast zero_lt_one) (le_min h1 hva)))
  let U : ↥W.DelF → (ZMod l)ˣ := fun δ => Units.mk0 _ (hne δ)
  have hUinj : Function.Injective U := by
    intro δ δ' h
    have h1 : ((aδ δ : ℕ) : ZMod l) = ((aδ δ' : ℕ) : ZMod l) := congrArg Units.val h
    rw [ZMod.natCast_eq_natCast_iff'] at h1
    set χd := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ : ↥(OL LL))
    set χd' := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ' : ↥(OL LL))

    have hdiff : (1 : WithTop ℚ) ≤ (D.loc l).v LL (χd - χd') := by
      have e : χd - χd' = (χd - (aδ δ : ↥LL.1)) - (χd' - (aδ δ' : ↥LL.1)) +
          ((aδ δ : ↥LL.1) - (aδ δ' : ↥LL.1)) := by ring
      rw [e]
      have hA1 := haδ δ
      have hA2 := haδ δ'
      rw [Nat.cast_one] at hA1 hA2
      refine le_trans (le_min (le_trans (le_min hA1 hA2) (AddValuation.map_sub ((D.loc l).v LL) _ _)) ?_)
        (AddValuation.map_add ((D.loc l).v LL) _ _)

      rcases le_total (aδ δ') (aδ δ) with hle | hle
      · have hd : l ∣ aδ δ - aδ δ' := (Nat.modEq_iff_dvd' hle).1 h1.symm
        obtain ⟨c, hc⟩ := hd
        have e2 : ((aδ δ : ℕ) : ↥LL.1) - ((aδ δ' : ℕ) : ↥LL.1) = ((aδ δ - aδ δ' : ℕ) : ↥LL.1) := by
          rw [Nat.cast_sub hle]
        rw [e2, hc, Nat.cast_mul, AddValuation.map_mul, hv]
        exact le_add_of_nonneg_right (Formalism.MainNotions.N.Pv.LocalLengthBound.Val.v_natCast_nonneg _ c)
      · have hd : l ∣ aδ δ' - aδ δ := (Nat.modEq_iff_dvd' hle).1 h1
        obtain ⟨c, hc⟩ := hd
        have e2 : ((aδ δ : ℕ) : ↥LL.1) - ((aδ δ' : ℕ) : ↥LL.1) = -((aδ δ' - aδ δ : ℕ) : ↥LL.1) := by
          rw [Nat.cast_sub hle]; ring
        rw [e2, AddValuation.map_neg, hc, Nat.cast_mul, AddValuation.map_mul, hv]
        exact le_add_of_nonneg_right (Formalism.MainNotions.N.Pv.LocalLengthBound.Val.v_natCast_nonneg _ c)

    set g := (δ : W.Gam) * (δ' : W.Gam)⁻¹
    have hξ : algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) = χd * χd'⁻¹ := by
      have hχ'0 : χd' ≠ 0 := by
        intro h0
        have := hvunit (W.χΓ δ')
        change (D.loc l).v LL χd' = 0 at this
        rw [h0, AddValuation.map_zero] at this
        exact WithTop.top_ne_coe this
      rw [eq_mul_inv_iff_mul_eq₀ hχ'0]
      simp only [χd, χd', g, ← map_mul, ← Units.val_mul, ← map_mul (W.χΓ), inv_mul_cancel_right]
    have hξ1 : (1 : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) - 1) := by
      have hχ'0 : χd' ≠ 0 := by
        intro h0
        have := hvunit (W.χΓ δ')
        change (D.loc l).v LL χd' = 0 at this
        rw [h0, AddValuation.map_zero] at this
        exact WithTop.top_ne_coe this
      have e : χd * χd'⁻¹ - 1 = (χd - χd') * χd'⁻¹ := by field_simp
      rw [hξ, e, AddValuation.map_mul]
      have hinv : (D.loc l).v LL χd'⁻¹ = 0 := by
        have := hvunit (W.χΓ δ')⁻¹
        simpa [χd', map_inv₀] using this
      rw [hinv, add_zero]
      exact hdiff

    obtain ⟨k, hk, hδk⟩ := (W.DelF_def δ).1 δ.2
    obtain ⟨k', hk', hδk'⟩ := (W.DelF_def δ').1 δ'.2
    have hgk : g ^ (k * k') = 1 := by
      simp only [g, mul_pow, inv_pow]
      rw [pow_mul, hδk, one_pow, one_mul, mul_comm k k', pow_mul, hδk', one_pow, inv_one]
    have hξk : (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL))) ^ (k * k') = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, hgk, map_one, Units.val_one, map_one]
    have hl3 : 3 ≤ l := by
      have h2 := (Fact.out : l.Prime).two_le
      have hodd : l ≠ 2 := hA.2.1
      omega
    have hξeq : algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) = 1 := by
      by_contra hne1
      exact Formalism.MainNotions.N.Pv.LocalLengthBound.Val.pow_ne_one_of_close ((D.loc l).v LL) (Fact.out : l.Prime) hv hl3
        (k * k') _ (Nat.mul_pos hk hk') hξ1 hne1 hξk
    have hg1 : g = 1 := by
      apply W.χΓ_inj
      rw [map_one]
      apply Units.ext
      apply Subtype.val_injective
      simpa using hξeq
    exact Subtype.ext (mul_inv_eq_one.1 hg1)
  have hUbij : Function.Bijective U := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hUinj, by rw [Fintype.card_coe, hcard, ZMod.card_units]⟩

  obtain ⟨b, hb, hζb⟩ := hζ.eq_pow_of_pow_eq_one hζ'.pow_eq_one
  have hb0 : ((b : ℕ) : ZMod l) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have : b = 0 := Nat.eq_zero_of_dvd_of_lt hd hb
    subst this
    rw [pow_zero] at hζb
    exact hζ'.ne_one (Fact.out : l.Prime).one_lt hζb.symm
  obtain ⟨δ, hδ⟩ := hUbij.2 (Units.mk0 _ hb0)
  have h1 : ((aδ δ : ℕ) : ZMod l) = ((b : ℕ) : ZMod l) := congrArg Units.val hδ
  rw [ZMod.natCast_eq_natCast_iff] at h1
  have hpowmod : ∀ m : ℕ, ζ ^ m = ζ ^ (m % l) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m l, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  refine ⟨δ, δ.2, aδ δ, ?_, haδ δ⟩
  rw [hpowmod, h1, ← hpowmod, hζb]

/- English proof (translation)
Introduce `D HW F Cm h4 h9 l _ K LL hA` and use `⟨clause_at_levels D HW F Cm h4 h9 l K LL hA, torsion_transitive D HW F h9 l K LL hA⟩`.
-/
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm → Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL),
      Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL hA.2.2) ∧
        Formalism.MainNotions.N.Pv.LocalLengthBound.PtTrans ((HW l).W K 1 LL hA.2.2) :=
  fun D HW F Cm h4 h9 l _ K LL hA =>
    ⟨clause_at_levels D HW F Cm h4 h9 l K LL hA, torsion_transitive D HW F h9 l K LL hA⟩

end GlobalTheory.LevelClauseOdd
