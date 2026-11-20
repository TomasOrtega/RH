import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.EvAtPsIff

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Fin

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR} (W : LocWach PD LL O v n)
    [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [hpF : Fact PD.p.Prime]
    [IsDomain O] [CharZero O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (F : Type) [Field F] [Algebra O F] [Algebra ℤ_[PD.p] O]

/- English proof (translation)
Establish `hl : 2 ≤ PD.p` using `hpF.out.two_le`. Establish `h0` using `(W.γ₀_X g).1`. Establish `h1 : PowerSeries.coeff 1 (W.γ₀ g PowerSeries.X) = algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p])`. Rewrite using `[(W.γ₀_X g).2, hz g]`. Establish `hbs` using `Formalism.MainNotions.UnusedSlot80.LG.aut_eq_bs W.φ₀ (W.γ₀ g) PD.p hl (Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W) (fun a => W.γ₀_comm g a) h0 (z g : ℤ_[PD.p]) h1`.

Use `set A := (PadicInt.toZModPow (s + 1) (z g : ℤ_[PD.p])).val with hA`. Establish `hyA : Polynomial.aeval ((ζ : F) ^ A - 1) (Zp (O` using `O) PD.p (s + 1)) = 0 := root_Zp PD.p (s + 1) (by rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul, rs_pow_N F PD.p s ζ, one_pow])`. Rewrite using `[evAt_apply, evAt_apply]`. Establish `e1 : (W.γA g x) a = W.γ₀ g (x a)` using `rfl`. Establish `huy : evR PD.p (s + 1) hlm (rs_root F s ζ) (W.γ₀ g PowerSeries.X) = (ζ : F) ^ A - 1`.

Establish `e : W.γ₀ g PowerSeries.X = PowerSeries.binomialSeries O (z g : ℤ_[PD.p]) - 1`. Rewrite using `[← hbs]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_sub, evR_bs PD.p hlm s (rs_root F s ζ) (ζ : F) rfl, map_one]`. Rewrite using `[e1, Formalism.MainNotions.UnusedSlot80.LG.algHom_eq_subst (W.γ₀ g) h0, evR_subst PD.p (s + 1) hlm (rs_root F s ζ) hyA _ h0 huy]`.

Conclude with `evR_congr PD.p (s + 1) hlm hyA _ rfl _`.
-/
theorem evAt_γ (z : W.Gam → ℤ_[PD.p]ˣ)
    (hz : ∀ g, algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) = (W.χΓ g : O)) (a : ZMod n) (s : ℕ)
    (g : W.Gam) (ζ : Rs F PD.p s) (x : LetA O n) :
    evAt hlm F a s ζ (W.γA g x) = evAt hlm F a s (powR F PD.p s (redU PD.p s (z g)) ζ) x := by
  have hl : 2 ≤ PD.p := hpF.out.two_le
  have h0 := (W.γ₀_X g).1
  have h1 : PowerSeries.coeff 1 (W.γ₀ g PowerSeries.X) = algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) := by
    rw [(W.γ₀_X g).2, hz g]
  have hbs := Formalism.MainNotions.UnusedSlot80.LG.aut_eq_bs W.φ₀ (W.γ₀ g) PD.p hl (Formalism.MainNotions.UnusedSlot80.LG.φ₀_X_eq W)
    (fun a => W.γ₀_comm g a) h0 (z g : ℤ_[PD.p]) h1
  set A := (PadicInt.toZModPow (s + 1) (z g : ℤ_[PD.p])).val with hA
  have hyA : Polynomial.aeval ((ζ : F) ^ A - 1) (Zp (O := O) PD.p (s + 1)) = 0 :=
    root_Zp PD.p (s + 1) (by rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul,
      rs_pow_N F PD.p s ζ, one_pow])
  rw [evAt_apply, evAt_apply]
  have e1 : (W.γA g x) a = W.γ₀ g (x a) := rfl
  have huy : evR PD.p (s + 1) hlm (rs_root F s ζ) (W.γ₀ g PowerSeries.X) = (ζ : F) ^ A - 1 := by
    have e : W.γ₀ g PowerSeries.X = PowerSeries.binomialSeries O (z g : ℤ_[PD.p]) - 1 := by
      rw [← hbs]; ring
    rw [e, map_sub, evR_bs PD.p hlm s (rs_root F s ζ) (ζ : F) rfl, map_one]
  rw [e1, Formalism.MainNotions.UnusedSlot80.LG.algHom_eq_subst (W.γ₀ g) h0,
    evR_subst PD.p (s + 1) hlm (rs_root F s ζ) hyA _ h0 huy]
  exact evR_congr PD.p (s + 1) hlm hyA _ rfl _

omit [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [IsDomain O] [CharZero O] in

/- English proof (translation)
Take `⟨z0, hz0, hv⟩` from `hγz`. Establish `hzg : z W.gam = z0` using `Units.ext (hZinj (by rw [hz, hz0]))`. Establish `hne : (z0 : ℤ_[PD.p]) - 1 ≠ 0`. Introduce `h`. Rewrite `hv` using `[h, PadicInt.valuation_zero]`.

Conclude with `zero_ne_one hv`. Establish `hu1 : (z0 : ℤ_[PD.p]) - 1 ∈ Ideal.span {((PD.p : ℕ) : ℤ_[PD.p])}`. Use `(PadicInt.mem_span_pow_iff_le_valuation _ hne 1).2 (by rw [hv])` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis. Establish `hu2 : (z0 : ℤ_[PD.p]) - 1 ∉ Ideal.span {((PD.p : ℕ) : ℤ_[PD.p]) ^ 2}`.

Introduce `h`. Use `(PadicInt.mem_span_pow_iff_le_valuation _ hne 2).1 h` as an intermediate fact. Rewrite `this` using `[hv]`. Use linear arithmetic over natural numbers and integers. Establish `htop` using `hGen PD.p hp2 s z0 hu1 hu2`.

Establish `hl2` using `hpF.out.two_le`. Take `⟨H, hH⟩ : ∃ H : Subgroup W.Gam, (H : Set W.Gam) = ↑W.DelF` from `⟨ { carrier := ↑W.DelF mul_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Finset.mem_coe, W.DelF_def] at ha hb ⊢`. Take `⟨k, hk, hak⟩` from `ha`.

Take `⟨k', hk', hbk⟩` from `hb`. Conclude with `⟨k * k', Nat.mul_pos hk hk', by`. Rewrite using `[mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm, pow_mul, hbk, one_pow]⟩`. Use the proof step `one_mem' := by`. Simplify using `only [Finset.mem_coe, W.DelF_def]`.

Conclude with `⟨1, one_pos, one_pow _⟩`. Use the proof step `inv_mem' := by`. Introduce `a ha`. Simplify using `only [Finset.mem_coe, W.DelF_def] at ha ⊢`. Take `⟨k, hk, hak⟩` from `ha`.

Conclude with `⟨k, hk, by rw [inv_pow, hak, inv_one]⟩ }, rfl⟩`. Establish `memH : ∀ x, x ∈ H ↔ x ∈ W.DelF` using `fun x => by`. Rewrite using `[← SetLike.mem_coe, hH, Finset.mem_coe]`. Establish `hHcard : Nat.card H = PD.p - 1`. Rewrite using `[← hcard, ← Nat.card_eq_finsetCard]`.

Conclude with `Nat.card_congr (Equiv.subtypeEquivRight memH)`. Establish `hexp : ∀ δ ∈ W.DelF, δ ^ (PD.p - 1) = 1`. Introduce `δ hδ`. Establish `h : (⟨δ, (memH δ).mpr hδ⟩ : H) ^ (PD.p - 1) = 1`. Rewrite using `[← hHcard]`.

Conclude with `pow_card_eq_one'`. Establish `h2` using `congrArg (fun y : H => (y : W.Gam)) h`. Simplify `h2` using `only [Subgroup.coe_pow, Subgroup.coe_one]`. Establish `hzΔ : ∀ δ : ↥W.DelF, (z δ) ^ (PD.p - 1) = 1`. Introduce `δ`.

Apply `Units.ext` to reduce the goal to its premises. Apply `hZinj` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val, map_pow, hz, ← Units.val_pow_eq_pow_val, ← map_pow, hexp δ δ.2, map_one]`. Simplify using the standard rewrite rules. Set `zΔ : ↥W.DelF → DeltaT PD.p` to `fun δ => ⟨z δ, hzΔ δ⟩`.

Establish `hinj : Function.Injective zΔ`. Introduce `δ δ' h`. Establish `h1 : z δ = z δ'` using `congrArg Subtype.val h`. Establish `h2 : W.χΓ δ = W.χΓ δ'` using `Units.ext (by rw [← hz, ← hz, h1])`. Conclude with `Subtype.ext (W.χΓ_inj h2)`.

Use `haveI : NeZero (PD.p - 1) := ⟨by omega⟩`. Set `e : DeltaT PD.p ≃ ↥(rootsOfUnity (PD.p - 1) ℤ_[PD.p])` to `Equiv.subtypeEquivRight fun x => (mem_rootsOfUnity (PD.p - 1) x).symm`. Use `haveI : Finite (DeltaT PD.p) := Finite.of_equiv _ e.symm`. Establish `hle : Nat.card (DeltaT PD.p) ≤ Nat.card ↥W.DelF`. Rewrite using `[Nat.card_congr e, Nat.card_eq_finsetCard, hcard]`.

Conclude with `card_rootsOfUnity ℤ_[PD.p] (PD.p - 1)`. Establish `hsurj` using `(hinj.bijective_of_nat_card_le hle).2`. Rewrite using `[eq_top_iff, ← htop]`. Apply `Subgroup.closure_mono` to reduce the goal to its premises. Introduce `u hu`.

Break down `Set.mem_insert_iff.1 hu with rfl | ⟨d, rfl⟩` into its components or cases. Conclude with `Set.mem_insert_iff.2 (Or.inl (by rw [hzg]))`. Take `⟨δ, hδ⟩` from `hsurj d`. Use `Set.mem_insert_of_mem _ ⟨δ, δ.2, ?_⟩` and prove the remaining obligations. Use `show redU PD.p s (z δ) = redU PD.p s d.1`.

Rewrite using `[← hδ]`.
-/
theorem gen_of (z : W.Gam → ℤ_[PD.p]ˣ)
    (hz : ∀ g, algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) = (W.χΓ g : O))
    (hZinj : Function.Injective (algebraMap ℤ_[PD.p] O))
    (hγz : ∃ z0 : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z0 : ℤ_[PD.p]) = (W.χΓ W.gam : O) ∧
      ((z0 : ℤ_[PD.p]) - 1).valuation = 1)
    (hcard : W.DelF.card = PD.p - 1) (hp2 : PD.p ≠ 2) (hGen : GenUnitsC) (s : ℕ) :
    Subgroup.closure (insert (redU PD.p s (z W.gam))
      ((fun g => redU PD.p s (z g)) '' (W.DelF : Set W.Gam))) = ⊤ := by
  obtain ⟨z0, hz0, hv⟩ := hγz
  have hzg : z W.gam = z0 := Units.ext (hZinj (by rw [hz, hz0]))
  have hne : (z0 : ℤ_[PD.p]) - 1 ≠ 0 := by
    intro h; rw [h, PadicInt.valuation_zero] at hv; exact zero_ne_one hv
  have hu1 : (z0 : ℤ_[PD.p]) - 1 ∈ Ideal.span {((PD.p : ℕ) : ℤ_[PD.p])} := by
    have := (PadicInt.mem_span_pow_iff_le_valuation _ hne 1).2 (by rw [hv])
    rwa [pow_one] at this
  have hu2 : (z0 : ℤ_[PD.p]) - 1 ∉ Ideal.span {((PD.p : ℕ) : ℤ_[PD.p]) ^ 2} := by
    intro h
    have := (PadicInt.mem_span_pow_iff_le_valuation _ hne 2).1 h
    rw [hv] at this; omega
  have htop := hGen PD.p hp2 s z0 hu1 hu2

  have hl2 := hpF.out.two_le
  obtain ⟨H, hH⟩ : ∃ H : Subgroup W.Gam, (H : Set W.Gam) = ↑W.DelF := ⟨
    { carrier := ↑W.DelF
      mul_mem' := by
        intro a b ha hb
        simp only [Finset.mem_coe, W.DelF_def] at ha hb ⊢
        obtain ⟨k, hk, hak⟩ := ha
        obtain ⟨k', hk', hbk⟩ := hb
        exact ⟨k * k', Nat.mul_pos hk hk', by
          rw [mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm, pow_mul, hbk, one_pow]⟩
      one_mem' := by
        simp only [Finset.mem_coe, W.DelF_def]
        exact ⟨1, one_pos, one_pow _⟩
      inv_mem' := by
        intro a ha
        simp only [Finset.mem_coe, W.DelF_def] at ha ⊢
        obtain ⟨k, hk, hak⟩ := ha
        exact ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩ }, rfl⟩
  have memH : ∀ x, x ∈ H ↔ x ∈ W.DelF := fun x => by
    rw [← SetLike.mem_coe, hH, Finset.mem_coe]
  have hHcard : Nat.card H = PD.p - 1 := by
    rw [← hcard, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight memH)
  have hexp : ∀ δ ∈ W.DelF, δ ^ (PD.p - 1) = 1 := by
    intro δ hδ
    have h : (⟨δ, (memH δ).mpr hδ⟩ : H) ^ (PD.p - 1) = 1 := by
      rw [← hHcard]
      exact pow_card_eq_one'
    have h2 := congrArg (fun y : H => (y : W.Gam)) h
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h2

  have hzΔ : ∀ δ : ↥W.DelF, (z δ) ^ (PD.p - 1) = 1 := by
    intro δ
    apply Units.ext
    apply hZinj
    rw [Units.val_pow_eq_pow_val, map_pow, hz, ← Units.val_pow_eq_pow_val, ← map_pow,
      hexp δ δ.2, map_one]
    simp
  let zΔ : ↥W.DelF → DeltaT PD.p := fun δ => ⟨z δ, hzΔ δ⟩
  have hinj : Function.Injective zΔ := by
    intro δ δ' h
    have h1 : z δ = z δ' := congrArg Subtype.val h
    have h2 : W.χΓ δ = W.χΓ δ' := Units.ext (by rw [← hz, ← hz, h1])
    exact Subtype.ext (W.χΓ_inj h2)
  haveI : NeZero (PD.p - 1) := ⟨by omega⟩
  let e : DeltaT PD.p ≃ ↥(rootsOfUnity (PD.p - 1) ℤ_[PD.p]) :=
    Equiv.subtypeEquivRight fun x => (mem_rootsOfUnity (PD.p - 1) x).symm
  haveI : Finite (DeltaT PD.p) := Finite.of_equiv _ e.symm
  have hle : Nat.card (DeltaT PD.p) ≤ Nat.card ↥W.DelF := by
    rw [Nat.card_congr e, Nat.card_eq_finsetCard, hcard]
    exact card_rootsOfUnity ℤ_[PD.p] (PD.p - 1)
  have hsurj := (hinj.bijective_of_nat_card_le hle).2
  rw [eq_top_iff, ← htop]
  apply Subgroup.closure_mono
  intro u hu
  rcases Set.mem_insert_iff.1 hu with rfl | ⟨d, rfl⟩
  · exact Set.mem_insert_iff.2 (Or.inl (by rw [hzg]))
  · obtain ⟨δ, hδ⟩ := hsurj d
    refine Set.mem_insert_of_mem _ ⟨δ, δ.2, ?_⟩
    show redU PD.p s (z δ) = redU PD.p s d.1
    rw [← hδ]

omit [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [IsDomain O] [CharZero O] in
/- English proof (translation)
The claim follows from `gen_of W z hz hZinj hγz hcard hp2 hGen s`.
-/
theorem gen_of' (z : W.Gam → ℤ_[PD.p]ˣ)
    (hz : ∀ g, algebraMap ℤ_[PD.p] O (z g : ℤ_[PD.p]) = (W.χΓ g : O))
    (hZinj : Function.Injective (algebraMap ℤ_[PD.p] O))
    (hγz : ∃ z0 : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z0 : ℤ_[PD.p]) = (W.χΓ W.gam : O) ∧
      ((z0 : ℤ_[PD.p]) - 1).valuation = 1)
    (hcard : W.DelF.card = PD.p - 1) (hp2 : PD.p ≠ 2) (hGen : GenUnitsC) (s : ℕ) :
    Subgroup.closure (insert ((fun g => redU PD.p s (z g)) W.gam)
      ((fun g => redU PD.p s (z g)) '' (W.DelF : Set W.Gam))) = ⊤ :=
  gen_of W z hz hZinj hγz hcard hp2 hGen s

def levBasics_of (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) [IsAlgClosed F] [CharZero F]
    (hinjF : Function.Injective (algebraMap O F))
    (hZinj : Function.Injective (algebraMap ℤ_[PD.p] O))
    (hχ : ∀ g : W.Gam, ∃ z : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z : ℤ_[PD.p]) = (W.χΓ g : O))
    (hγz : ∃ z0 : ℤ_[PD.p]ˣ, algebraMap ℤ_[PD.p] O (z0 : ℤ_[PD.p]) = (W.χΓ W.gam : O) ∧
      ((z0 : ℤ_[PD.p]) - 1).valuation = 1)
    (hcard : W.DelF.card = PD.p - 1) (hp2 : PD.p ≠ 2) (hGen : GenUnitsC) (a : ZMod n) (s : ℕ) :
    LevBasics W a s where
  F := F
  fF := inferInstance
  algOF := inferInstance
  inj := hinjF
  hp := Nat.cast_ne_zero.2 hpF.out.ne_zero
  root := exists_prim _ (pow_pos hpF.out.pos _)
  ev := evAt hlm F a s
  ev_O ζ x := by
    rw [evAt_apply]
    exact (evR PD.p (s + 1) hlm (rs_root F s ζ)).commutes x
  ev_letE ζ := by
    rw [evAt_apply]
    simp [letE]
  ev_π ζ := by
    rw [evAt_apply]
    exact evR_X PD.p (s + 1) hlm (rs_root F s ζ)
  ev_ps ζ := (evAt_ps_iff W hlm F hR a s s ζ).2 rfl
  ev_pt t ht ζ := fun h => ht ((evAt_ps_iff W hlm F hR a s t ζ).1 h)
  σ g := redU PD.p s (Classical.choose (hχ g))
  ev_γ g ζ x := evAt_γ W hlm F (fun g => Classical.choose (hχ g))
    (fun g => Classical.choose_spec (hχ g)) a s g ζ x
  gen := gen_of' W (fun g => Classical.choose (hχ g)) (fun g => Classical.choose_spec (hχ g))
    hZinj hγz hcard hp2 hGen s

end Fin

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
