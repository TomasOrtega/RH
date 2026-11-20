import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.PrimeNotMemBasePlace
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing Filter GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open UpperTheory.V.Z.Desc.V0
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

/- English proof (translation)
Use `haveI : CharP (O ⧸ maximalIdeal O) l := inferInstanceAs (CharP (ResidueField O) l)`. Use `haveI : PerfectRing (ResidueField O) l := inferInstance`. Set `j : ResidueField O →+* Perfection (O ⧸ maximalIdeal O) l` to `Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O) (RingHom.id (ResidueField O))`. Establish `hj : ∀ x, Perfection.coeff (O ⧸ maximalIdeal O) l 0 (j x) = x` using `fun x => by`. Use `(Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O)).symm_apply_apply (RingHom.id (ResidueField O))` as an intermediate fact.

Conclude with `RingHom.congr_fun this x`. Use `⟨(Perfection.teichmuller l (maximalIdeal O)).comp j, fun x => ?_⟩` and prove the remaining obligations. Conclude with `(Perfection.mk_teichmuller (j x)).trans (hj x)`.
-/
private theorem ce_teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := inferInstanceAs (CharP (ResidueField O) l)
  haveI : PerfectRing (ResidueField O) l := inferInstance
  let j : ResidueField O →+* Perfection (O ⧸ maximalIdeal O) l :=
    Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O) (RingHom.id (ResidueField O))
  have hj : ∀ x, Perfection.coeff (O ⧸ maximalIdeal O) l 0 (j x) = x := fun x => by
    have := (Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O)).symm_apply_apply (RingHom.id (ResidueField O))
    exact RingHom.congr_fun this x
  refine ⟨(Perfection.teichmuller l (maximalIdeal O)).comp j, fun x => ?_⟩
  exact (Perfection.mk_teichmuller (j x)).trans (hj x)

/- English proof (translation)
Take `⟨hc, hfin, hlm, -⟩` from `UpperTheory.V.abelian₂.dvr_finite l c.O`. Use `haveI : Finite (ResidueField c.O) := hfin`. Use `haveI : CharP (ResidueField c.O) l := by`. Use `(CharP.charP_iff_prime_eq_zero hl.out).2 ?_` and prove the remaining obligations. Rewrite using `[← map_natCast (residue c.O), residue_eq_zero_iff]`.

Conclude with `hlm`. Take `⟨τ, hτ⟩` from `ce_teich_ex l c.O`. Use `⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]`.
-/
private theorem ce_isTeich {l : ℕ} [hl : Fact l.Prime] {F : W.GFrame l} (c : Coef l) {n : ℕ} (r : Resid F c.O n) :
    ∃ t, r.IsTeich t := by
  obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  obtain ⟨τ, hτ⟩ := ce_teich_ex l c.O
  refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩⟩
  rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]

/- English proof (translation)
Establish `: ((Matrix.GeneralLinearGroup.map f).comp τ).ker = τ.ker`. Use `MonoidHom.ker_comp_of_injective _ _ fun a b hab => ?_` and prove the remaining obligations. Use extensionality with `i j`. Conclude with `hf (congrArg (fun x : GL (Fin m) ℂ => (x : Matrix (Fin m) (Fin m) ℂ) i j) hab)`. Rewrite `h` using `[this]`. Then use the resulting hypothesis.
-/
private theorem ce_open {G O : Type} [Group G] [TopologicalSpace G] [CommRing O] {m : ℕ} (f : O →+* ℂ) (hf : Function.Injective f)
    (τ : G →* GL (Fin m) O) (h : IsOpen (((Matrix.GeneralLinearGroup.map f).comp τ).ker : Set G)) : IsOpen (τ.ker : Set G) := by
  have : ((Matrix.GeneralLinearGroup.map f).comp τ).ker = τ.ker := by
    refine MonoidHom.ker_comp_of_injective _ _ fun a b hab => ?_
    ext i j
    exact hf (congrArg (fun x : GL (Fin m) ℂ => (x : Matrix (Fin m) (Fin m) ℂ) i j) hab)
  rwa [this] at h

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hZ` to reduce the goal to its premises. Rewrite using `[← Submodule.finrank_eq_zero, hsum]`. Conclude with `Finset.sum_eq_zero fun i _ => by rw [h i, finrank_bot]`.
-/
private theorem ce_ex {M J : Type} [AddCommGroup M] [Module ℂ M] [Fintype J] (Y : J → Submodule ℂ M) (Z : Submodule ℂ M)
    (hf : FiniteDimensional ℂ Z) (hZ : Z ≠ ⊥) (hsum : Module.finrank ℂ Z = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z)) :
    ∃ i, Y i ⊓ Z ≠ ⊥ := by
  by_contra h
  push Not at h
  apply hZ
  rw [← Submodule.finrank_eq_zero, hsum]
  exact Finset.sum_eq_zero fun i _ => by rw [h i, finrank_bot]

private def ce_mk {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {n : ℕ} {s : HidaSetting l L Ω} (V : s.Lev) (hS : ∀ v ∈ s.S, IsSplitAt (s.w v)) (τ : ∀ w : Plc L, SmIrr (GLw n w))
    (σ : Submodule ℂ (UA L n → ℂ)) (h : ∀ w, IsSplitAt w → Cp σ w (τ w)) : Comps V σ where
  l v := τ (s.w v.1)
  u v := τ (s.w v)
  o := τ (s.w s.v0)
  hl v := h _ (hS _ (Or.inl v.2))
  hu v := h _ (hS _ (Or.inr (Or.inl v.2)))
  ho := h _ (hS _ (Or.inr (Or.inr rfl)))

/- English proof (translation)
Introduce `h'` and use `h (by rw [h', bot_inf_eq])`.
-/
private theorem ce_ne {M : Type} [AddCommGroup M] [Module ℂ M] {Y Z : Submodule ℂ M} (h : Y ⊓ Z ≠ ⊥) : Y ≠ ⊥ :=
  fun h' => h (by rw [h', bot_inf_eq])

section Set

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l}
  {H : HSet L Ω l n c} {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] {θ : H.X.I.T →* Aˣ} {ι : Qbar l ≃+* ℂ}
  {x : A →+* Qbar l} {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ} {c0 : ℕ}
  {sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d}

/- English proof (translation)
The claim follows from `haveI := hsp.fin K c0 le_rfl Submodule.finiteDimensional_of_le (S₂ := H.ClAt θ ι x lam ξ K c0) (inf_le_left.trans (iSup_le fun _ => inf_le_left))`.
-/
private theorem ce_fin (hsp : H.IsSpec θ ι x lam ξ c0 sp) (K : H.Lev) (ev : H.Op → ℂ) :
    FiniteDimensional ℂ (zPart H θ ι x lam ξ K c0 ev) :=
  haveI := hsp.fin K c0 le_rfl
  Submodule.finiteDimensional_of_le (S₂ := H.ClAt θ ι x lam ξ K c0) (inf_le_left.trans (iSup_le fun _ => inf_le_left))

/- English proof (translation)
Use `hEP L n H.V H.Sl τ c0 _ _ fun v => ?_` and prove the remaining obligations. Use `hO1 N _ n _ _ (τ _).smooth (τ _).irred c0 _ _ (fun i y hy => ?_) (hSl L Ω l n c H hAx ι lam v (fun j => ev (.inr (v, j))) (hev v))` and prove the remaining obligations. Rewrite using `[hsp.triv v i y hy, map_one, inv_one]`.
-/
private theorem ce_one (hSl : Slope) (hO1 : Ord1) (hEP : EigPi) (N : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hAx : H.Ax)
    (hsp : H.IsSpec θ ι x lam ξ c0 sp) (ev : H.Op → ℂ) (hev : ∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1)
    (τ : ∀ v, SmIrr (GLw n (H.Sl v))) :
    Module.rank ℂ (eigL H.Sl (piRep fun v => (τ v).ρ) c0 (fun v i y => (ι (H.finPart θ x lam v i y))⁻¹)
      fun v j => H.lowVal ι lam v (j + 1) * ev (.inr (v, j))) ≤ 1 := by
  refine hEP L n H.V H.Sl τ c0 _ _ fun v => ?_
  refine hO1 N _ n _ _ (τ _).smooth (τ _).irred c0 _ _ (fun i y hy => ?_)
    (hSl L Ω l n c H hAx ι lam v (fun j => ev (.inr (v, j))) (hev v))
  rw [hsp.triv v i y hy, map_one, inv_one]

end Set

section Stg

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  (s : HidaSetting l L Ω)

/- English proof (translation)
Use extensionality with `x`. Conclude with `(s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)`.
-/
private theorem ce_w (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

/- English proof (translation)
The claim follows from `UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω (s.A _) _ (s.hA _) (s.split _ h) w rfl`.
-/
private theorem ce_split (w : Plc L) (h : w.under (𝓞 (Lp L)) ∈ s.S) : IsSplitAt w :=
  UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω (s.A _) _ (s.hA _) (s.split _ h) w rfl

/- English proof (translation)
The claim follows from `ce_split s _ ((ce_w s v).symm ▸ h)`.
-/
private theorem ce_S (v : Plc (Lp L)) (h : v ∈ s.S) : IsSplitAt (s.w v) := ce_split s _ ((ce_w s v).symm ▸ h)

/- English proof (translation)
Establish `hpr : Function.Surjective V.pr` using `fun g => by`. Take `⟨τ, hτ⟩ : ∃ τ, ReciprocityTheory.Gal.toGS Ω V.S' τ = g.1` from `QuotientGroup.mk_surjective g.1`. Take `⟨t, rfl⟩` from `(V.hη τ).1 (by rw [hτ]; exact g.2)`. Conclude with `⟨t, Subtype.ext hτ⟩`. Use `⟨hi.1, fun _ _ _ => Submodule.mem_top, fun M hM hI => hi.2.2 M hM fun g => ?_⟩` and prove the remaining obligations.

Take `⟨g, rfl⟩` from `hpr g`. Conclude with `hI g`.
-/
private theorem ce_irr (V : s.Lev) {n : ℕ} (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) (hi : Af.IsIrr ρ) : Af.IsIrr (ρ.comp V.pr) := by
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, ReciprocityTheory.Gal.toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨t, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨t, Subtype.ext hτ⟩
  refine ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun M hM hI => hi.2.2 M hM fun g => ?_⟩
  obtain ⟨g, rfl⟩ := hpr g
  exact hI g

end Stg

/- English proof (translation)
Simplify using `[ePart, opE]`.
-/
private theorem eigenpart_zero_eq_top {G R W : Type} [Group G] [CommRing R] [AddCommGroup W] [Module R W] (ρ : Representation R G W) :
    ePart ρ (0 : G →₀ ℤ) 0 = ⊤ := by
  simp [ePart, opE]

/- English proof (translation)
Substitute `hE` using the available equality. Establish `h : ∀ S : Submodule ℂ M, Module.finrank ℂ ↥(S ⊓ ⊤) = Module.finrank ℂ S` using `fun S => by rw [inf_top_eq]`. Simplify `hsum` using `only [h]`.
-/
private theorem ce_top {M J : Type} [AddCommGroup M] [Module ℂ M] [Fintype J] (Y : J → Submodule ℂ M) (Z E : Submodule ℂ M) (hE : E = ⊤)
    (hsum : Module.finrank ℂ ↥(Z ⊓ E) = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z ⊓ E)) :
    Module.finrank ℂ Z = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z) := by
  subst hE
  have h : ∀ S : Submodule ℂ M, Module.finrank ℂ ↥(S ⊓ ⊤) = Module.finrank ℂ S := fun S => by rw [inf_top_eq]
  simpa only [h] using hsum

/- English proof (translation)
Substitute `hE` using the available equality. Break down `Cardinal.le_one_iff.1 ha with h | h` into its components or cases. Rewrite `h3` using `[h, zero_mul, Submodule.rank_eq_zero, inf_top_eq, ← h2]`. Conclude with `absurd h3 h0`. Conclude with `h`.
-/
private theorem cardinal_factor_eq_one {M : Type} [AddCommGroup M] [Module ℂ M] (Y Z ZL E : Submodule ℂ M) (hE : E = ⊤) (h0 : Y ⊓ Z ≠ ⊥) (h2 : Y ⊓ Z = Y ⊓ ZL)
    (a b : Cardinal) (ha : a ≤ 1) (h3 : Module.rank ℂ ↥(Y ⊓ ZL ⊓ E) = a * b) : a = 1 := by
  subst hE
  rcases Cardinal.le_one_iff.1 ha with h | h
  · rw [h, zero_mul, Submodule.rank_eq_zero, inf_top_eq, ← h2] at h3
    exact absurd h3 h0
  · exact h

/- English proof (translation)
Establish `h6 : ∀ i, (Module.finrank ℂ ↥(Y i ⊓ Z ⊓ E) : Cardinal) = if P i then b else 0` using `fun i => by haveI : FiniteDimensional ℂ ↥(Y i ⊓ Z ⊓ E) := Submodule.finiteDimensional_of_le (inf_le_left.trans inf_le_right)`. Rewrite using `[Module.finrank_eq_rank]`. Use `split_ifs with h`. Rewrite using `[h2 i h, h3 i h, ha1, one_mul]`. Rewrite using `[Submodule.rank_eq_zero]`.

Assume the negation of the conclusion as `h'`. Use `h (h1 i fun h'' => h' ?_)` and prove the remaining obligations. Rewrite using `[h'', bot_inf_eq]`. Rewrite using `[hsum, Nat.cast_sum, Finset.sum_congr rfl fun i _ => h6 i, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← hk, Nat.card_eq_fintype_card, Fintype.card_subtype]`.
-/
private theorem ce_cnt {M J : Type} [AddCommGroup M] [Module ℂ M] [Fintype J] (Y : J → Submodule ℂ M) (Z ZL E : Submodule ℂ M)
    (hf : FiniteDimensional ℂ Z) (hsum : Module.finrank ℂ ↥(Z ⊓ E) = ∑ i, Module.finrank ℂ ↥(Y i ⊓ Z ⊓ E)) (P : J → Prop)
    (a b : Cardinal) (k : ℕ) (h1 : ∀ i, Y i ⊓ Z ≠ ⊥ → P i) (h2 : ∀ i, P i → Y i ⊓ Z = Y i ⊓ ZL) (ha1 : a = 1)
    (h3 : ∀ i, P i → Module.rank ℂ ↥(Y i ⊓ ZL ⊓ E) = a * b) (hk : Nat.card {i // P i} = k) :
    (Module.finrank ℂ ↥(Z ⊓ E) : Cardinal) = k * b := by
  classical
  have h6 : ∀ i, (Module.finrank ℂ ↥(Y i ⊓ Z ⊓ E) : Cardinal) = if P i then b else 0 := fun i => by
    haveI : FiniteDimensional ℂ ↥(Y i ⊓ Z ⊓ E) := Submodule.finiteDimensional_of_le (inf_le_left.trans inf_le_right)
    rw [Module.finrank_eq_rank]
    split_ifs with h
    · rw [h2 i h, h3 i h, ha1, one_mul]
    · rw [Submodule.rank_eq_zero]
      by_contra h'
      refine h (h1 i fun h'' => h' ?_)
      rw [h'', bot_inf_eq]
  rw [hsum, Nat.cast_sum, Finset.sum_congr rfl fun i _ => h6 i, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← hk,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `hWt hDec hZD _ hSph hAt hBc hYD _ hSl hO1 hEP PH hM hCO l _ L Ω _ _ _ _ _ _ s n hn V hV h4 ι lam`. Establish `N` using `PH.toClassicalTheorems.litN`. Establish `hU : GlobalTheory.BCT.Unr L` using `UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr`. Take `⟨lam', hl'⟩` from `hWt l L Ω s n hn V hV ι lam`. Take `⟨a₀, -, ha⟩` from `hM L hU n hn h4 lam'`.

Use `⟨a₀, ?_⟩` and prove the remaining obligations. Introduce `Q c r m τ₀ hτ d e ξ he A _ _ _ θ x c0 sp hθ hsp K ev hev hZ hP`. Establish `hAx` using `axU N l L Ω s n hn V Q c m τ₀`. Establish `hS` using `ce_S s`. Take `⟨t, ht⟩` from `ce_isTeich c r`.

Establish `hop : IsOpen (τ₀.ker : Set (KT n (wt s)))` using `ce_open _ (ι.injective.comp Subtype.val_injective) τ₀ (hτ t ht).1`. Take `⟨S, K', J, _, σ, hSec, hLev, hKL, hID, hInd, hUn, hFix, hLe⟩` from `hDec l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he hop lam' hl' c0`. Establish `hA : ∀ i, IsAutRepU (σ i)` using `fun i => (hID.1 i).1`. Establish `hsumE` using `fun (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) (h : ∀ g ∈ a.support, g ∈ KO _ (Fin n)) => hZD l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he A θ x c0 sp hθ hsp K ev hev J σ hA hInd hLe a N h`. Establish `he0 : eC Q τ₀ d (0 : GLw n (s.w s.v0) →₀ ℤ) 0 = ⊤` using `eigenpart_zero_eq_top _`.

Establish `hsum` using `ce_top (fun i => YOf Q ι τ₀ e ξ (σ i)) _ _ he0 (hsumE 0 0 (by simp))`. Establish `hfin` using `ce_fin hsp K ev`. Take `⟨i0, h0⟩` from `ce_ex (fun i => YOf Q ι τ₀ e ξ (σ i)) _ hfin hZ hsum`. Establish `hY0 : YOf Q ι τ₀ e ξ (σ i0) ≠ ⊥` using `ce_ne h0`. Take `⟨Y, hY, -, -, hLG⟩` from `partU PH l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he (σ i0) (hA i0) hY0`.

Establish `hi` using `hP Y (by rw [hY]; exact h0)`. Establish `hc : Continuous (Y.r.comp V.pr)` using `Y.cont.comp (V.pr_cont W.continuous_resP)`. Take `⟨π, hreg, hcsd, hat, hinf, hsat⟩` from `hBc PH L Ω hU l s.odd ι n hn (σ i0) (hA i0) (Y.r.comp V.pr) hc (ce_irr s V Y.r hi) (Eventually.of_forall hLG)`. Establish `hns : ∀ w : Plc L, ¬ IsSplitAt w → w.under (𝓞 (Lp L)) ∉ s.S` using `fun w h h' => h (ce_split s w h')`. Use `choose τ hτπ using fun w => (Af.locCompC PH.toClassicalTheorems L n π w).1`.

Establish `hCp : ∀ i, At π (σ i) → ∀ w, IsSplitAt w → Cp (σ i) w (τ w)` using `fun i h w hw => hCO L hU n hn h4 π hreg hcsd (σ i) (hA i) (fun w hw => hUn i w (hns w hw)) h w hw _ (hτπ w)`. Establish `hcard` using `ha π hreg hcsd (fun v => hinf _ _ ((hID.1 i0).2.1 v)) (fun w hw => hsat w (hUn i0 w (hns w hw))) S hSec K' hLev (fun w hw => hKL w (hns w hw)) (fun w hwS hw => ⟨τ w, hτπ w, hFix i0 w hwS hw _ (hCp i0 hat w hw)⟩) J σ hID`. Establish `h1` using `fun i h => hAt N l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he A θ x c0 sp hθ hsp K ev _ _ (hA i0) (hA i) h0 h π hat`. Establish `h2` using `fun i (h : At π (σ i)) => hSph N l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he A θ x c0 sp hθ hsp K ev hev _ _ (hA i0) (hA i) (fun w hw => ⟨τ w, hCp i0 hat w hw, hCp i h w hw⟩) h0`. Establish `h3` using `fun (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) i (h : At π (σ i)) => hYD l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he (σ i) (hA i) (hUn i) ((hl' _ (hA i)).2 (hID.1 i).2.1) (ce_mk V hS τ (σ i) (hCp i h)) c0 (fun v i y => (ι ((hset Q τ₀).finPart θ x.toRingHom lam v i y))⁻¹) (fun v j => (hset …`.

Establish `h5` using `ce_one hSl hO1 hEP N hAx hsp ev hev fun v => τ (s.w v.1)`. Establish `ha1` using `cardinal_factor_eq_one _ _ _ _ he0 h0 (h2 i0 hat) _ _ h5 (h3 0 0 i0 hat)`. Use `⟨π, σ i0, ce_mk V hS τ (σ i0) (hCp i0 hat), fun u => hτπ _, hτπ _, hY0, hA i0, fun a N' hs => ?_⟩` and prove the remaining obligations. Conclude with `ce_cnt (fun i => YOf Q ι τ₀ e ξ (σ i)) _ _ _ hfin (hsumE a N' hs) (fun i => At π (σ i)) _ _ a₀ h1 h2 ha1 (h3 a N') hcard`.
-/
theorem UpperTheory.V.Z.Desc.V0.countE :
    UpperTheory.V.Z.J.D.WtEx → UpperTheory.V.Z.J.D.Decomp → ZDecE → UpperTheory.V.Z.J.D.ZEq → UpperTheory.V.Z.J.D.SphSame → UpperTheory.V.Z.J.D.AtSame → UpperTheory.V.Z.J.D.BcOf → YDimE → UpperTheory.V.Z.J.D.CompsEx → UpperTheory.V.Z.J.D.Slope → UpperTheory.V.Z.J.D.Ord1 → UpperTheory.V.Z.J.D.EigPi → CountE := by
  intro hWt hDec hZD _ hSph hAt hBc hYD _ hSl hO1 hEP PH hM hCO l _ L Ω _ _ _ _ _ _ s n hn V hV h4 ι lam
  have N := PH.toClassicalTheorems.litN
  have hU : GlobalTheory.BCT.Unr L := UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr
  obtain ⟨lam', hl'⟩ := hWt l L Ω s n hn V hV ι lam
  obtain ⟨a₀, -, ha⟩ := hM L hU n hn h4 lam'
  refine ⟨a₀, ?_⟩
  intro Q c r m τ₀ hτ d e ξ he A _ _ _ θ x c0 sp hθ hsp K ev hev hZ hP
  have hAx := axU N l L Ω s n hn V Q c m τ₀
  have hS := ce_S s
  obtain ⟨t, ht⟩ := ce_isTeich c r
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) :=
    ce_open _ (ι.injective.comp Subtype.val_injective) τ₀ (hτ t ht).1
  obtain ⟨S, K', J, _, σ, hSec, hLev, hKL, hID, hInd, hUn, hFix, hLe⟩ :=
    hDec l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he hop lam' hl' c0
  have hA : ∀ i, IsAutRepU (σ i) := fun i => (hID.1 i).1
  have hsumE := fun (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) (h : ∀ g ∈ a.support, g ∈ KO _ (Fin n)) =>
    hZD l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he A θ x c0 sp hθ hsp K ev hev J σ hA hInd hLe a N h
  have he0 : eC Q τ₀ d (0 : GLw n (s.w s.v0) →₀ ℤ) 0 = ⊤ := eigenpart_zero_eq_top _
  have hsum := ce_top (fun i => YOf Q ι τ₀ e ξ (σ i)) _ _ he0 (hsumE 0 0 (by simp))
  have hfin := ce_fin hsp K ev
  obtain ⟨i0, h0⟩ := ce_ex (fun i => YOf Q ι τ₀ e ξ (σ i)) _ hfin hZ hsum
  have hY0 : YOf Q ι τ₀ e ξ (σ i0) ≠ ⊥ := ce_ne h0
  obtain ⟨Y, hY, -, -, hLG⟩ := partU PH l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he (σ i0) (hA i0) hY0
  have hi := hP Y (by rw [hY]; exact h0)
  have hc : Continuous (Y.r.comp V.pr) := Y.cont.comp (V.pr_cont W.continuous_resP)
  obtain ⟨π, hreg, hcsd, hat, hinf, hsat⟩ := hBc PH L Ω hU l s.odd ι n hn (σ i0) (hA i0) (Y.r.comp V.pr) hc (ce_irr s V Y.r hi)
    (Eventually.of_forall hLG)
  have hns : ∀ w : Plc L, ¬ IsSplitAt w → w.under (𝓞 (Lp L)) ∉ s.S := fun w h h' => h (ce_split s w h')
  choose τ hτπ using fun w => (Af.locCompC PH.toClassicalTheorems L n π w).1
  have hCp : ∀ i, At π (σ i) → ∀ w, IsSplitAt w → Cp (σ i) w (τ w) := fun i h w hw =>
    hCO L hU n hn h4 π hreg hcsd (σ i) (hA i) (fun w hw => hUn i w (hns w hw)) h w hw _ (hτπ w)
  have hcard := ha π hreg hcsd (fun v => hinf _ _ ((hID.1 i0).2.1 v)) (fun w hw => hsat w (hUn i0 w (hns w hw))) S hSec K' hLev
    (fun w hw => hKL w (hns w hw)) (fun w hwS hw => ⟨τ w, hτπ w, hFix i0 w hwS hw _ (hCp i0 hat w hw)⟩) J σ hID
  have h1 := fun i h => hAt N l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he A θ x c0 sp hθ hsp K ev _ _ (hA i0) (hA i) h0 h π hat
  have h2 := fun i (h : At π (σ i)) => hSph N l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he A θ x c0 sp hθ hsp K ev hev _ _ (hA i0) (hA i)
      (fun w hw => ⟨τ w, hCp i0 hat w hw, hCp i h w hw⟩) h0
  have h3 := fun (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) i (h : At π (σ i)) =>
    hYD l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ he (σ i) (hA i) (hUn i) ((hl' _ (hA i)).2 (hID.1 i).2.1)
      (ce_mk V hS τ (σ i) (hCp i h)) c0 (fun v i y => (ι ((hset Q τ₀).finPart θ x.toRingHom lam v i y))⁻¹)
      (fun v j => (hset Q τ₀).lowVal ι lam v (j + 1) * ev (.inr (v, j))) a N
  have h5 := ce_one hSl hO1 hEP N hAx hsp ev hev fun v => τ (s.w v.1)
  have ha1 := cardinal_factor_eq_one _ _ _ _ he0 h0 (h2 i0 hat) _ _ h5 (h3 0 0 i0 hat)
  refine ⟨π, σ i0, ce_mk V hS τ (σ i0) (hCp i0 hat), fun u => hτπ _, hτπ _, hY0, hA i0, fun a N' hs => ?_⟩
  exact ce_cnt (fun i => YOf Q ι τ₀ e ξ (σ i)) _ _ _ hfin (hsumE a N' hs) (fun i => At π (σ i)) _ _ a₀ h1 h2 ha1 (h3 a N') hcard
