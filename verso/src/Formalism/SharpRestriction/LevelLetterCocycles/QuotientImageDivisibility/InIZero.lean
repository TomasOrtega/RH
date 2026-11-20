import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.MemPreG

set_option linter.unusedVariables false

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section P4

variable (W : LocWach PD LL O v n)

/- English proof (translation)
Use `⟨⟨by simp, fun δ _ => map_zero _⟩, ⟨0, 0, by simp⟩, ⟨0, (W.N T).zero_mem, fun δ _ => map_zero _, by simp⟩⟩` and prove the remaining obligations.
-/
theorem inI_zero (T : LocLat G Qp LL O) (i : ZMod n) : Formalism.MainNotions.CrystallineLiftingInputs.InI W T i 0 := by
  refine ⟨⟨by simp, fun δ _ => map_zero _⟩, ⟨0, 0, by simp⟩, ⟨0, (W.N T).zero_mem,
    fun δ _ => map_zero _, by simp⟩⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using inI_zero W T i`. Consider the case `insert k s hk ih`. Rewrite using `[Finset.sum_insert hk]`. Conclude with `Formalism.MainNotions.RamifiedCoefficientChains.S9.inI_add W T (Formalism.MainNotions.RamifiedCoefficientChains.S9.inI_smul W T _ (hx k (Finset.mem_insert_self _ _))) (ih fun j hj => hx j (Finset.mem_insert_of_mem hj))`.
-/
theorem inI_sum (T : LocLat G Qp LL O) (i : ZMod n) {ι : Type} (s : Finset ι) (a : ι → O)
    (x : ι → W.DD T) (hx : ∀ k ∈ s, Formalism.MainNotions.CrystallineLiftingInputs.InI W T i (x k)) :
    Formalism.MainNotions.CrystallineLiftingInputs.InI W T i (∑ k ∈ s, a k • x k) := by
  induction s using Finset.induction_on with
  | empty => simpa using inI_zero W T i
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    exact Formalism.MainNotions.RamifiedCoefficientChains.S9.inI_add W T (Formalism.MainNotions.RamifiedCoefficientChains.S9.inI_smul W T _ (hx k (Finset.mem_insert_self _ _)))
      (ih fun j hj => hx j (Finset.mem_insert_of_mem hj))

end P4

section Pass4

variable (W : LocWach PD LL O v n)

/- English proof (translation)
Establish `hp : (PD.p : LL) ≠ 0` using `Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W`. Establish `hQ : W.Q = W.q` using `Q_eq_q W hs`. Use `set Fη := Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-(η : ℤ)) with hFη`. Use `set F0 := Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 0 with hF0`. Set `dH : ↥F3 →+ (ℤ → T₂.V ⊗[Qp] BdR)` to `{ toFun := d, map_zero' := by`.

Establish `h` using `hda 0 0`. Rewrite `h` using `[add_zero]`. Use `congrArg (fun z => z - d 0) h` as an intermediate fact. Simplify using `using this.symm`. Use the proof step `map_add' := hda }`.

Take `⟨r, bF⟩` from `Submodule.basisOfPid (Module.Free.chooseBasis O FF) F3`. Establish `hk : ∀ k : Fin r, ∃ ell, ell ∈ (fun z => φVB PD (LL` using `LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) z)) '' Formalism.MainNotions.CrystallineLiftingInputs.Dlat W T₂ (c - 1 - 1 - 1) ∧ ell ∈ C ∧ (PD.p : LL) ^ e₂ • d (bF k) 0 - (PD.p : LL) ^ κ • ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) ell) ∈ Fη := fun k => by`. Take `⟨ell, h1, h2, h3⟩` from `hell (bF k)`. Conclude with `⟨ell, h1, h2, h3⟩`. Use `choose ell hellD hellC hellF using hk`.

Establish `hky : ∀ k : Fin r, ∃ y : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c y ∧ ∃ hB : W.Q ^ Bn • W.map F y ∈ W.N T₂, ∀ (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ (u : PowerSeries LL), W.lev c ζ W.q = X * u → constantCoeff u ≠ 0 → ∀ (dd : ℤ → T₂.V ⊗[Qp] BdR), (∃ m₀, LB …` using `LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ell k)) ∧ ∀ i : ℤ, dd i ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ c := fun k => hL41 (ell k) (hellD k) (hellC k)`. Use `choose yk hykI hykB hykE using hky`. Use `set yL : ↥F3 →ₗ[O] W.DD T₁ := bF.constr O yk with hyL`. Use `set ellF : ↥F3 → T₂.V ⊗[Qp] B := fun f => ∑ k, algebraMap O LL (bF.repr f k) • ell k with hellFdef`. Establish `hyLf : ∀ f, yL f = ∑ k, bF.repr f k • yk k` using `fun f => (bF.constr_apply O yk f).trans (Finsupp.sum_fintype _ _ (by simp))`.

Establish `hdsum : ∀ f, d f = ∑ k, algebraMap O LL (bF.repr f k) • d (bF k)`. Introduce `f`. Use `conv_lhs => rw [← bF.sum_repr f]`. Use `show dH (∑ k, bF.repr f k • bF k) = _`. Rewrite using `[map_sum]`.

Conclude with `Finset.sum_congr rfl fun k _ => hds _ _`. Establish `hA : ∀ f, (PD.p : LL) ^ e₂ • d f 0 - (PD.p : LL) ^ κ • ιV PD (LL` using `LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ellF f)) ∈ Fη := by`. Introduce `f`. Establish `e1 : d f 0 = ∑ k, algebraMap O LL (bF.repr f k) • d (bF k) 0`. Rewrite using `[hdsum f, Finset.sum_apply]`.

Both sides reduce to the same expression. Establish `e2 : ιV PD (LL` using `LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ellF f)) = ∑ k, algebraMap O LL (bF.repr f k) • ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ell k)) := by`. Simplify using `only [hellFdef, map_sum, map_smul]`. Rewrite using `[e1, e2, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations.

Use `Fη.smul_mem (algebraMap O LL (bF.repr f k)) (hellF k)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[smul_sub, smul_comm _ (algebraMap O LL (bF.repr f k)), smul_comm _ (algebraMap O LL (bF.repr f k))]`. Establish `hellF0 : ellF 0 = 0` using `by simp [hellFdef]`. Establish `hellFa : ∀ f g, ellF (f + g) = ellF f + ellF g`.

Introduce `f g`. Simplify using `only [hellFdef, map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]`. Establish `hellFs : ∀ (o : O) f, ellF (o • f) = algebraMap O LL o • ellF f`. Introduce `o f`. Simplify using `only [hellFdef, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]`.

Set `ψ4 : ↥F3 →+ (T₂.V ⊗[Qp] BdR) ⧸ F0` to `{ toFun := fun f => F0.mkQ ((PD.p : LL) ^ e₂ • d f 0 - (PD.p : LL) ^ κ • ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ellF f))) map_zero' := by`. Establish `h0 : d 0 = 0` using `dH.map_zero`. Simplify using `[h0, hellF0]`. Use the proof step `map_add' := fun f g => by`. Rewrite using `[← map_add]`.

Use `congr 1`. Rewrite using `[hda, hellFa]`. Simplify using `only [Pi.add_apply, map_add, smul_add]`. Use `abel }`. Establish `hψ4 : ∀ (o : O) (x : ↥F3), ψ4 (o • x) = algebraMap O LL o • ψ4 x`.

Introduce `o x`. Use `show F0.mkQ _ = algebraMap O LL o • F0.mkQ _`. Establish `hX : (PD.p : LL) ^ e₂ • d (o • x) 0 - (PD.p : LL) ^ κ • ιV PD (LL` using `LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ellF (o • x))) = algebraMap O LL o • ((PD.p : LL) ^ e₂ • d x 0 - (PD.p : LL) ^ κ • ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ellF x))) := by`. Rewrite using `[hds, hellFs]`. Simplify using `only [Pi.smul_apply, map_smul, smul_sub]`.

Rewrite using `[smul_comm _ (algebraMap O LL o), smul_comm _ (algebraMap O LL o)]`. Rewrite using `[hX, map_smul]`. Establish `hrank4 : Module.finrank LL ↥(Submodule.span LL (Set.range ψ4)) ≤ m`. Establish `hsub : Submodule.span LL (Set.range ψ4) ≤ Fη.map F0.mkQ`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨f, rfl⟩`. Conclude with `⟨_, hA f, rfl⟩`. Conclude with `(Submodule.finrank_mono hsub).trans hrk`. Establish `ch4` using `pchain_of_gen (pstep_rank (lenO := lenOl PD (O := O)) (m := m) (c := cc) F3 ψ4 hψ4 hrank4)`. Use `set F4 := zeroSub F3 ψ4 hψ4 with hF4def`.

Establish `hF4 : F4 ≤ F3` using `zeroSub_le F3 ψ4 hψ4`. Use `⟨F4, hF4, yL.comp (Submodule.inclusion hF4), ch4, fun f => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Use `show Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c (yL (Submodule.inclusion hF4 f))`. Rewrite using `[hyLf]`. Conclude with `inI_sum W T₁ c _ _ _ (fun k _ => hykI k)`.

Use `set f3 := Submodule.inclusion hF4 f with hf3 show Formalism.MainNotions.RamifiedCoefficientChains.S9.Hyp6 W T₂ c (((PD.p : O) ^ e₂) • w f3 - W.map F (yL f3))`. Establish `hyI : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c (yL f3)`. Rewrite using `[hyLf]`. Conclude with `inI_sum W T₁ c _ _ _ (fun k _ => hykI k)`. Establish `hmapy : W.map F (yL f3) = ∑ k, bF.repr f3 k • W.map F (yk k)`.

Rewrite using `[hyLf, map_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => Formalism.MainNotions.UnusedSlot80.ArcC.map_smulO W F _ _`. Establish `hFyD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ c (W.map F (yL f3))` using `⟨by rw [← Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, hyI.1.1], fun δ hδ => by rw [← W.map_γ, hyI.1.2 δ hδ]⟩`. Establish `hwD'` using `hwD f3`. Establish `hw'D : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ c (((PD.p : O) ^ e₂) • w f3 - W.map F (yL f3))`.

Use `⟨?_, fun δ hδ => ?_⟩` and prove the remaining obligations. Rewrite using `[smul_sub, osmul_comm W T₂, hwD'.1, hFyD.1]`. Rewrite using `[map_sub, map_smul, hwD'.2 δ hδ, hFyD.2 δ hδ]`. Establish `hB : W.Q ^ Bn • W.map F (yL f3) ∈ W.N T₂`. Rewrite using `[hmapy, Finset.smul_sum]`.

Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[osmul_comm W T₂, ← algebraMap_smul (LetA O n)]`. Conclude with `(W.N T₂).smul_mem _ (hykB k)`. Establish `hKy : W.Q ^ (η + Bn) • W.map F (yL f3) ∈ W.N T₂`. Rewrite using `[pow_add, mul_smul]`.

Conclude with `(W.N T₂).smul_mem _ hB`. Establish `hK' : W.Q ^ (η + Bn) • (((PD.p : O) ^ e₂) • w f3 - W.map F (yL f3)) ∈ W.N T₂`. Rewrite using `[smul_sub, osmul_comm W T₂]`. Use `(W.N T₂).sub_mem ?_ hKy` and prove the remaining obligations. Rewrite using `[← algebraMap_smul (LetA O n)]`.

Conclude with `(W.N T₂).smul_mem _ (hwK f3)`. Establish `hexk : ∀ k, ∃ dk : ℤ → T₂.V ⊗[Qp] BdR, (∃ m₀, LB m₀ dk) ∧ W.levN T₂ c ζ₀ ⟨W.Q ^ Bn • W.map F (yk k), hykB k⟩ = smulS ((X * u₀) ^ Bn) dk`. Introduce `k`. Take `⟨m₁, hm₁⟩` from `W.levN_supp T₂ c ζ₀ ⟨W.Q ^ Bn • W.map F (yk k), hykB k⟩`. Take `⟨dk, h1, h2⟩` from `div_exists hm₁ u₀ hu0 Bn`.

Conclude with `⟨dk, ⟨_, h1⟩, h2.symm⟩`. Use `choose dk hdkLB hdke using hexk`. Establish `hdkP` using `fun k => hykE k ζ₀ hζ₀ u₀ hu₀ hu0 (dk k) (hdkLB k) (hdke k)`. Use `choose mk hmk using hdkLB`. Take `⟨md, hmd⟩` from `hdLB f3`.

Use `set M : ℤ := -(|md| + ∑ k, |mk k|) with hM`. Establish `hMk : ∀ k, M ≤ mk k` using `fun k => by`. Establish `h1 : |mk k| ≤ ∑ j, |mk j|` using `Finset.single_le_sum (f := fun j => |mk j|) (fun j _ => abs_nonneg _) (Finset.mem_univ k)`. Establish `h2` using `neg_abs_le (mk k)`. Establish `h3` using `abs_nonneg md`.

Use linear arithmetic over natural numbers and integers. Establish `hMd : M ≤ md`. Establish `h1 : 0 ≤ ∑ j, |mk j|` using `Finset.sum_nonneg fun j _ => abs_nonneg _`. Establish `h2` using `neg_abs_le md`. Use linear arithmetic over natural numbers and integers.

Establish `hLBk : ∀ k, LB M (dk k)` using `fun k => LB_mono (hmk k) (hMk k)`. Use `set ddy : ℤ → T₂.V ⊗[Qp] BdR := ∑ k, algebraMap O LL (bF.repr f3 k) • dk k with hddy`. Establish `hLBy : LB M ddy`. Introduce `j hj`. Simplify using `only [hddy, Finset.sum_apply, Pi.smul_apply, hLBk _ j hj, smul_zero, Finset.sum_const_zero]`.

Establish `hsumS : ∀ (g : PowerSeries LL) (s : Finset (Fin r)), smulS g (∑ k ∈ s, algebraMap O LL (bF.repr f3 k) • dk k) = ∑ k ∈ s, algebraMap O LL (bF.repr f3 k) • smulS g (dk k)`. Introduce `g s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => funext j`. Simplify using `[smulS]`.

Consider the case `insert k s hk ih`. Establish `hLBs : LB M (∑ k ∈ s, algebraMap O LL (bF.repr f3 k) • dk k)`. Introduce `j hj`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, hLBk _ j hj, smul_zero, Finset.sum_const_zero]`. Rewrite using `[Finset.sum_insert hk, Finset.sum_insert hk, smulS_add (LB_smul (hLBk k) _) hLBs, smulS_smul (hLBk k), ih]`.

Establish `hlevB : W.levN T₂ c ζ₀ ⟨W.Q ^ Bn • W.map F (yL f3), hB⟩ = smulS ((X * u₀) ^ Bn) ddy`. Establish `e1 : (⟨W.Q ^ Bn • W.map F (yL f3), hB⟩ : ↥(W.N T₂)) = ∑ k, bF.repr f3 k • (⟨W.Q ^ Bn • W.map F (yk k), hykB k⟩ : ↥(W.N T₂))`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show W.Q ^ Bn • W.map F (yL f3) = ((∑ k, bF.repr f3 k • (⟨W.Q ^ Bn • W.map F (yk k), hykB k⟩ : ↥(W.N T₂)) : ↥(W.N T₂)) : W.DD T₂)`. Rewrite using `[hmapy, Finset.smul_sum, Submodule.coe_sum]`.

Conclude with `Finset.sum_congr rfl fun k _ => by show W.Q ^ Bn • (bF.repr f3 k • W.map F (yk k)) = bF.repr f3 k • (W.Q ^ Bn • W.map F (yk k))`. Conclude with `osmul_comm W T₂ _ _ _`. Rewrite using `[e1, map_sum, hddy, hsumS]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [levN_osmul W T₂ c ζ₀, hdke k]`. Establish `hlevy : W.levN T₂ c ζ₀ ⟨W.Q ^ (η + Bn) • W.map F (yL f3), hKy⟩ = smulS ((X * u₀) ^ (η + Bn)) ddy`.

Establish `e1 : (⟨W.Q ^ (η + Bn) • W.map F (yL f3), hKy⟩ : ↥(W.N T₂)) = W.Q ^ η • (⟨W.Q ^ Bn • W.map F (yL f3), hB⟩ : ↥(W.N T₂))` using `Subtype.ext (by show W.Q ^ (η + Bn) • W.map F (yL f3) = W.Q ^ η • (W.Q ^ Bn • W.map F (yL f3))`. Rewrite using `[pow_add, mul_smul])`. Establish `e2 : W.levN T₂ c ζ₀ (W.Q ^ η • (⟨W.Q ^ Bn • W.map F (yL f3), hB⟩ : ↥(W.N T₂))) = smulS (W.lev c ζ₀ (W.Q ^ η)) (W.levN T₂ c ζ₀ ⟨W.Q ^ Bn • W.map F (yL f3), hB⟩)`. Use function extensionality and compare the values at `fun j => W.levN_smul T₂ c ζ₀ _ _ j`. Rewrite using `[e1, e2, hlevB, map_pow, hQ, hu₀, ← smulS_mul hLBy, ← pow_add]`.

Establish `hlev' : W.levN T₂ c ζ₀ ⟨W.Q ^ (η + Bn) • (((PD.p : O) ^ e₂) • w f3 - W.map F (yL f3)), hK'⟩ = smulS ((X * u₀) ^ (η + Bn)) (((PD.p : LL) ^ e₂) • d f3 - ddy)`. Establish `e1 : (⟨W.Q ^ (η + Bn) • (((PD.p : O) ^ e₂) • w f3 - W.map F (yL f3)), hK'⟩ : ↥(W.N T₂)) = ((PD.p : O) ^ e₂) • (⟨W.Q ^ (η + Bn) • w f3, hwK f3⟩ : ↥(W.N T₂)) - ⟨W.Q ^ (η + Bn) • W.map F (yL f3), hKy⟩` using `Subtype.ext (by show W.Q ^ (η + Bn) • (((PD.p : O) ^ e₂) • w f3 - W.map F (yL f3)) = ((PD.p : O) ^ e₂) • (W.Q ^ (η + Bn) • w f3) - W.Q ^ (η + Bn) • W.map F (yL f3)`. Rewrite using `[smul_sub, osmul_comm W T₂])`. Rewrite using `[e1, map_sub, levN_osmul W T₂ c ζ₀, hde f3, hlevy, smulS_sub (LB_smul (LB_mono hmd hMd) _) hLBy, smulS_smul (LB_mono hmd hMd), map_pow, map_natCast]`. Establish `hFil : ∀ i : ℤ, ((((PD.p : LL) ^ e₂) • d f3 - ddy) i) ∈ Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-i)`.

Introduce `i`. Establish `hddyi : ddy i = ∑ k, algebraMap O LL (bF.repr f3 k) • dk k i`. Simplify using `only [hddy, Finset.sum_apply, Pi.smul_apply]`. Simplify using `only [Pi.sub_apply, Pi.smul_apply]`. Distinguish the cases in `hi0 : i = 0`.

Substitute `hi0` using the available equality. Establish `hz : ψ4 f3 = 0` using `(mem_zeroSub_coe F3 ψ4 hψ4 f3).1 f.2`. Establish `hz' : (PD.p : LL) ^ e₂ • d f3 0 - (PD.p : LL) ^ κ • ιV PD (LL` using `LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ellF f3)) ∈ F0 := (Submodule.Quotient.mk_eq_zero F0).1 hz`. Establish `hd0 : ddy 0 = (PD.p : LL) ^ κ • ιV PD (LL` using `LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ellF f3)) := by`. Rewrite using `[hddyi]`.

Simplify using `only [hellFdef, map_sum, map_smul, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [(hdkP k).2.1, smul_comm]`. Rewrite using `[hd0, neg_zero]`. Conclude with `hz'`. Distinguish the cases in `hiB : i < (Bn : ℤ)`.

Establish `h0 : ddy i = 0`. Rewrite using `[hddyi]`. Conclude with `Finset.sum_eq_zero fun k _ => by rw [(hdkP k).1 i hiB hi0, smul_zero]`. Rewrite using `[h0, sub_zero]`. Conclude with `Submodule.smul_mem _ _ (hdF f3 i hi0)`.

Establish `hD : ddy i ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ c`. Rewrite using `[hddyi]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ((hdkP k).2.2 i)`. Conclude with `Submodule.sub_mem _ (Submodule.smul_mem _ _ (hdF f3 i hi0)) (hlow i (by omega) hD)`. Conclude with `⟨mem_of_exp W T₂ hs hR hMC hT₂ c ζ₀ hTr u₀ hu₀ hw'D.1 hw'D.2 hK' ⟨M, LB_sub (LB_smul (LB_mono hmd hMd) _) hLBy⟩ hlev' hFil, hw'D⟩`.
-/
theorem pass4 [NeZero n] [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O LL]
    (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (hT₁ : IsCrys PD T₁.ρ) (hT₂ : IsCrys PD T₂.ρ) (hMC : MemCrit W)
    (c : ZMod n) (ζ₀ : LL)
    (hTr : ∀ ζ : LL, IsPrimitiveRoot ζ PD.p → ∃ δ ∈ W.DelF, ∃ χ : LL, χ ≠ 0 ∧
      (∀ (x : ↥(W.N T₂)) (hx : W.γD T₂ δ x ∈ W.N T₂) (k : ℤ),
        W.levN T₂ c ζ ⟨W.γD T₂ δ x, hx⟩ k = χ ^ k • W.levN T₂ c ζ₀ x k) ∧
      (∀ f : LetA O n, W.lev c ζ (W.γA δ f) = PowerSeries.rescale χ (W.lev c ζ₀ f)))
    (u₀ : PowerSeries LL) (hu₀ : W.lev c ζ₀ W.q = X * u₀) (hu0 : constantCoeff u₀ ≠ 0)
    {Bn η e₂ m : ℕ} {κ : ℤ} {cc : ℝ} (hB1 : 1 ≤ Bn)
    (hlow : ∀ i : ℤ, (Bn : ℤ) ≤ i → Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ c ≤ Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-i))
    [FiniteDimensional LL ↥(Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-(η : ℤ)))]
    (hrk : Module.finrank LL ↥((Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-(η : ℤ))).map
      (Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 0).mkQ) ≤ m)
    (C : Submodule LL (T₂.V ⊗[Qp] B))
    {FF : Type} [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
    (F3 : Submodule O FF) (w : ↥F3 →ₗ[O] W.DD T₂)
    (hwD : ∀ f, Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ c (w f)) (hwK : ∀ f, W.Q ^ (η + Bn) • w f ∈ W.N T₂)
    (d : ↥F3 → ℤ → T₂.V ⊗[Qp] BdR) (hdLB : ∀ f, ∃ m₀, LB m₀ (d f))
    (hde : ∀ f, W.levN T₂ c ζ₀ ⟨W.Q ^ (η + Bn) • w f, hwK f⟩ = smulS ((X * u₀) ^ (η + Bn)) (d f))
    (hdF : ∀ f (i : ℤ), i ≠ 0 → d f i ∈ Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-i))
    (hda : ∀ f g, d (f + g) = d f + d g) (hds : ∀ (o : O) f, d (o • f) = algebraMap O LL o • d f)
    (hell : ∀ f, ∃ ell ∈ (fun z => φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) z)) ''
        Formalism.MainNotions.CrystallineLiftingInputs.Dlat W T₂ (c - 1 - 1 - 1), ell ∈ C ∧
      (PD.p : LL) ^ e₂ • d f 0 - (PD.p : LL) ^ κ •
          ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) ell) ∈
        Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-(η : ℤ)))
    (hL41 : ∀ ell ∈ (fun z => φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) z)) ''
        Formalism.MainNotions.CrystallineLiftingInputs.Dlat W T₂ (c - 1 - 1 - 1), ell ∈ C →
      ∃ y : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c y ∧
        ∃ hB : W.Q ^ Bn • W.map F y ∈ W.N T₂,
        ∀ (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ (u : PowerSeries LL),
          W.lev c ζ W.q = X * u → constantCoeff u ≠ 0 →
        ∀ (dd : ℤ → T₂.V ⊗[Qp] BdR), (∃ m₀, LB m₀ dd) →
          W.levN T₂ c ζ ⟨W.Q ^ Bn • W.map F y, hB⟩ = smulS ((X * u) ^ Bn) dd →
          (∀ i : ℤ, i < (Bn : ℤ) → i ≠ 0 → dd i = 0) ∧
          dd 0 = ((PD.p : LL) ^ κ) • ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) ell) ∧
          ∀ i : ℤ, dd i ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ c)
    (hζ₀ : IsPrimitiveRoot ζ₀ PD.p) :
    ∃ (F4 : Submodule O FF) (hF4 : F4 ≤ F3) (y : ↥F4 →ₗ[O] W.DD T₁),
      Formalism.MainNotions.RamifiedCoefficientChains.S9.PChain (lenOl PD (O := O)) m cc F3 F4 1 0 ∧
      ∀ f : ↥F4, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c (y f) ∧
        Formalism.MainNotions.RamifiedCoefficientChains.S9.Hyp6 W T₂ c (((PD.p : O) ^ e₂) • w (Submodule.inclusion hF4 f) - W.map F (y f)) := by
  classical
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  have hQ : W.Q = W.q := Q_eq_q W hs
  set Fη := Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-(η : ℤ)) with hFη
  set F0 := Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 0 with hF0

  let dH : ↥F3 →+ (ℤ → T₂.V ⊗[Qp] BdR) :=
    { toFun := d, map_zero' := by
        have h := hda 0 0
        rw [add_zero] at h
        have := congrArg (fun z => z - d 0) h
        simpa using this.symm
      map_add' := hda }

  obtain ⟨r, bF⟩ := Submodule.basisOfPid (Module.Free.chooseBasis O FF) F3
  have hk : ∀ k : Fin r, ∃ ell, ell ∈ (fun z => φVB PD (LL := LL) (V := T₂.V)
      (φVB PD (LL := LL) (V := T₂.V) z)) '' Formalism.MainNotions.CrystallineLiftingInputs.Dlat W T₂ (c - 1 - 1 - 1) ∧ ell ∈ C ∧
      (PD.p : LL) ^ e₂ • d (bF k) 0 - (PD.p : LL) ^ κ •
        ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) ell) ∈ Fη := fun k => by
    obtain ⟨ell, h1, h2, h3⟩ := hell (bF k)
    exact ⟨ell, h1, h2, h3⟩
  choose ell hellD hellC hellF using hk
  have hky : ∀ k : Fin r, ∃ y : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c y ∧
      ∃ hB : W.Q ^ Bn • W.map F y ∈ W.N T₂,
      ∀ (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ (u : PowerSeries LL),
        W.lev c ζ W.q = X * u → constantCoeff u ≠ 0 →
      ∀ (dd : ℤ → T₂.V ⊗[Qp] BdR), (∃ m₀, LB m₀ dd) →
        W.levN T₂ c ζ ⟨W.Q ^ Bn • W.map F y, hB⟩ = smulS ((X * u) ^ Bn) dd →
        (∀ i : ℤ, i < (Bn : ℤ) → i ≠ 0 → dd i = 0) ∧
        dd 0 = ((PD.p : LL) ^ κ) • ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ell k)) ∧
        ∀ i : ℤ, dd i ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ c := fun k => hL41 (ell k) (hellD k) (hellC k)
  choose yk hykI hykB hykE using hky
  set yL : ↥F3 →ₗ[O] W.DD T₁ := bF.constr O yk with hyL
  set ellF : ↥F3 → T₂.V ⊗[Qp] B := fun f => ∑ k, algebraMap O LL (bF.repr f k) • ell k with hellFdef
  have hyLf : ∀ f, yL f = ∑ k, bF.repr f k • yk k := fun f =>
    (bF.constr_apply O yk f).trans (Finsupp.sum_fintype _ _ (by simp))
  have hdsum : ∀ f, d f = ∑ k, algebraMap O LL (bF.repr f k) • d (bF k) := by
    intro f
    conv_lhs => rw [← bF.sum_repr f]
    show dH (∑ k, bF.repr f k • bF k) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hds _ _

  have hA : ∀ f, (PD.p : LL) ^ e₂ • d f 0 - (PD.p : LL) ^ κ •
      ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ellF f)) ∈ Fη := by
    intro f
    have e1 : d f 0 = ∑ k, algebraMap O LL (bF.repr f k) • d (bF k) 0 := by
      rw [hdsum f, Finset.sum_apply]; rfl
    have e2 : ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ellF f)) =
        ∑ k, algebraMap O LL (bF.repr f k) •
          ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ell k)) := by
      simp only [hellFdef, map_sum, map_smul]
    rw [e1, e2, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun k _ => ?_
    have := Fη.smul_mem (algebraMap O LL (bF.repr f k)) (hellF k)
    convert this using 1
    rw [smul_sub, smul_comm _ (algebraMap O LL (bF.repr f k)),
      smul_comm _ (algebraMap O LL (bF.repr f k))]
  have hellF0 : ellF 0 = 0 := by simp [hellFdef]
  have hellFa : ∀ f g, ellF (f + g) = ellF f + ellF g := by
    intro f g
    simp only [hellFdef, map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
  have hellFs : ∀ (o : O) f, ellF (o • f) = algebraMap O LL o • ellF f := by
    intro o f
    simp only [hellFdef, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]
  let ψ4 : ↥F3 →+ (T₂.V ⊗[Qp] BdR) ⧸ F0 :=
    { toFun := fun f => F0.mkQ ((PD.p : LL) ^ e₂ • d f 0 - (PD.p : LL) ^ κ •
        ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ellF f)))
      map_zero' := by
        have h0 : d 0 = 0 := dH.map_zero
        simp [h0, hellF0]
      map_add' := fun f g => by
        rw [← map_add]
        congr 1
        rw [hda, hellFa]
        simp only [Pi.add_apply, map_add, smul_add]
        abel }
  have hψ4 : ∀ (o : O) (x : ↥F3), ψ4 (o • x) = algebraMap O LL o • ψ4 x := by
    intro o x
    show F0.mkQ _ = algebraMap O LL o • F0.mkQ _
    have hX : (PD.p : LL) ^ e₂ • d (o • x) 0 - (PD.p : LL) ^ κ •
        ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ellF (o • x))) =
        algebraMap O LL o • ((PD.p : LL) ^ e₂ • d x 0 - (PD.p : LL) ^ κ •
        ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ellF x))) := by
      rw [hds, hellFs]
      simp only [Pi.smul_apply, map_smul, smul_sub]
      rw [smul_comm _ (algebraMap O LL o), smul_comm _ (algebraMap O LL o)]
    rw [hX, map_smul]
  have hrank4 : Module.finrank LL ↥(Submodule.span LL (Set.range ψ4)) ≤ m := by
    have hsub : Submodule.span LL (Set.range ψ4) ≤ Fη.map F0.mkQ := by
      rw [Submodule.span_le]
      rintro _ ⟨f, rfl⟩
      exact ⟨_, hA f, rfl⟩
    exact (Submodule.finrank_mono hsub).trans hrk
  have ch4 := pchain_of_gen (pstep_rank (lenO := lenOl PD (O := O)) (m := m) (c := cc) F3 ψ4 hψ4 hrank4)
  set F4 := zeroSub F3 ψ4 hψ4 with hF4def
  have hF4 : F4 ≤ F3 := zeroSub_le F3 ψ4 hψ4
  refine ⟨F4, hF4, yL.comp (Submodule.inclusion hF4), ch4, fun f => ⟨?_, ?_⟩⟩
  · show Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c (yL (Submodule.inclusion hF4 f))
    rw [hyLf]
    exact inI_sum W T₁ c _ _ _ (fun k _ => hykI k)
  · set f3 := Submodule.inclusion hF4 f with hf3
    show Formalism.MainNotions.RamifiedCoefficientChains.S9.Hyp6 W T₂ c (((PD.p : O) ^ e₂) • w f3 - W.map F (yL f3))
    have hyI : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c (yL f3) := by
      rw [hyLf]; exact inI_sum W T₁ c _ _ _ (fun k _ => hykI k)
    have hmapy : W.map F (yL f3) = ∑ k, bF.repr f3 k • W.map F (yk k) := by
      rw [hyLf, map_sum]
      exact Finset.sum_congr rfl fun k _ => Formalism.MainNotions.UnusedSlot80.ArcC.map_smulO W F _ _
    have hFyD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ c (W.map F (yL f3)) :=
      ⟨by rw [← Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, hyI.1.1], fun δ hδ => by rw [← W.map_γ, hyI.1.2 δ hδ]⟩
    have hwD' := hwD f3
    have hw'D : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ c (((PD.p : O) ^ e₂) • w f3 - W.map F (yL f3)) := by
      refine ⟨?_, fun δ hδ => ?_⟩
      · rw [smul_sub, osmul_comm W T₂, hwD'.1, hFyD.1]
      · rw [map_sub, map_smul, hwD'.2 δ hδ, hFyD.2 δ hδ]
    have hB : W.Q ^ Bn • W.map F (yL f3) ∈ W.N T₂ := by
      rw [hmapy, Finset.smul_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [osmul_comm W T₂, ← algebraMap_smul (LetA O n)]
      exact (W.N T₂).smul_mem _ (hykB k)
    have hKy : W.Q ^ (η + Bn) • W.map F (yL f3) ∈ W.N T₂ := by
      rw [pow_add, mul_smul]; exact (W.N T₂).smul_mem _ hB
    have hK' : W.Q ^ (η + Bn) • (((PD.p : O) ^ e₂) • w f3 - W.map F (yL f3)) ∈ W.N T₂ := by
      rw [smul_sub, osmul_comm W T₂]
      refine (W.N T₂).sub_mem ?_ hKy
      rw [← algebraMap_smul (LetA O n)]
      exact (W.N T₂).smul_mem _ (hwK f3)

    have hexk : ∀ k, ∃ dk : ℤ → T₂.V ⊗[Qp] BdR, (∃ m₀, LB m₀ dk) ∧
        W.levN T₂ c ζ₀ ⟨W.Q ^ Bn • W.map F (yk k), hykB k⟩ = smulS ((X * u₀) ^ Bn) dk := by
      intro k
      obtain ⟨m₁, hm₁⟩ := W.levN_supp T₂ c ζ₀ ⟨W.Q ^ Bn • W.map F (yk k), hykB k⟩
      obtain ⟨dk, h1, h2⟩ := div_exists hm₁ u₀ hu0 Bn
      exact ⟨dk, ⟨_, h1⟩, h2.symm⟩
    choose dk hdkLB hdke using hexk
    have hdkP := fun k => hykE k ζ₀ hζ₀ u₀ hu₀ hu0 (dk k) (hdkLB k) (hdke k)
    choose mk hmk using hdkLB
    obtain ⟨md, hmd⟩ := hdLB f3
    set M : ℤ := -(|md| + ∑ k, |mk k|) with hM
    have hMk : ∀ k, M ≤ mk k := fun k => by
      have h1 : |mk k| ≤ ∑ j, |mk j| :=
        Finset.single_le_sum (f := fun j => |mk j|) (fun j _ => abs_nonneg _) (Finset.mem_univ k)
      have h2 := neg_abs_le (mk k)
      have h3 := abs_nonneg md
      omega
    have hMd : M ≤ md := by
      have h1 : 0 ≤ ∑ j, |mk j| := Finset.sum_nonneg fun j _ => abs_nonneg _
      have h2 := neg_abs_le md
      omega
    have hLBk : ∀ k, LB M (dk k) := fun k => LB_mono (hmk k) (hMk k)
    set ddy : ℤ → T₂.V ⊗[Qp] BdR := ∑ k, algebraMap O LL (bF.repr f3 k) • dk k with hddy
    have hLBy : LB M ddy := by
      intro j hj
      simp only [hddy, Finset.sum_apply, Pi.smul_apply, hLBk _ j hj, smul_zero, Finset.sum_const_zero]
    have hsumS : ∀ (g : PowerSeries LL) (s : Finset (Fin r)),
        smulS g (∑ k ∈ s, algebraMap O LL (bF.repr f3 k) • dk k) =
          ∑ k ∈ s, algebraMap O LL (bF.repr f3 k) • smulS g (dk k) := by
      intro g s
      induction s using Finset.induction_on with
      | empty => funext j; simp [smulS]
      | insert k s hk ih =>
        have hLBs : LB M (∑ k ∈ s, algebraMap O LL (bF.repr f3 k) • dk k) := by
          intro j hj
          simp only [Finset.sum_apply, Pi.smul_apply, hLBk _ j hj, smul_zero, Finset.sum_const_zero]
        rw [Finset.sum_insert hk, Finset.sum_insert hk, smulS_add (LB_smul (hLBk k) _) hLBs,
          smulS_smul (hLBk k), ih]
    have hlevB : W.levN T₂ c ζ₀ ⟨W.Q ^ Bn • W.map F (yL f3), hB⟩ = smulS ((X * u₀) ^ Bn) ddy := by
      have e1 : (⟨W.Q ^ Bn • W.map F (yL f3), hB⟩ : ↥(W.N T₂)) =
          ∑ k, bF.repr f3 k • (⟨W.Q ^ Bn • W.map F (yk k), hykB k⟩ : ↥(W.N T₂)) := by
        apply Subtype.ext
        show W.Q ^ Bn • W.map F (yL f3) = ((∑ k, bF.repr f3 k •
          (⟨W.Q ^ Bn • W.map F (yk k), hykB k⟩ : ↥(W.N T₂)) : ↥(W.N T₂)) : W.DD T₂)
        rw [hmapy, Finset.smul_sum, Submodule.coe_sum]
        exact Finset.sum_congr rfl fun k _ => by
          show W.Q ^ Bn • (bF.repr f3 k • W.map F (yk k)) =
            bF.repr f3 k • (W.Q ^ Bn • W.map F (yk k))
          exact osmul_comm W T₂ _ _ _
      rw [e1, map_sum, hddy, hsumS]
      exact Finset.sum_congr rfl fun k _ => by rw [levN_osmul W T₂ c ζ₀, hdke k]
    have hlevy : W.levN T₂ c ζ₀ ⟨W.Q ^ (η + Bn) • W.map F (yL f3), hKy⟩ =
        smulS ((X * u₀) ^ (η + Bn)) ddy := by
      have e1 : (⟨W.Q ^ (η + Bn) • W.map F (yL f3), hKy⟩ : ↥(W.N T₂)) =
          W.Q ^ η • (⟨W.Q ^ Bn • W.map F (yL f3), hB⟩ : ↥(W.N T₂)) :=
        Subtype.ext (by
          show W.Q ^ (η + Bn) • W.map F (yL f3) = W.Q ^ η • (W.Q ^ Bn • W.map F (yL f3))
          rw [pow_add, mul_smul])
      have e2 : W.levN T₂ c ζ₀ (W.Q ^ η • (⟨W.Q ^ Bn • W.map F (yL f3), hB⟩ : ↥(W.N T₂))) =
          smulS (W.lev c ζ₀ (W.Q ^ η)) (W.levN T₂ c ζ₀ ⟨W.Q ^ Bn • W.map F (yL f3), hB⟩) :=
        funext fun j => W.levN_smul T₂ c ζ₀ _ _ j
      rw [e1, e2, hlevB, map_pow, hQ, hu₀, ← smulS_mul hLBy, ← pow_add]
    have hlev' : W.levN T₂ c ζ₀ ⟨W.Q ^ (η + Bn) • (((PD.p : O) ^ e₂) • w f3 - W.map F (yL f3)), hK'⟩ =
        smulS ((X * u₀) ^ (η + Bn)) (((PD.p : LL) ^ e₂) • d f3 - ddy) := by
      have e1 : (⟨W.Q ^ (η + Bn) • (((PD.p : O) ^ e₂) • w f3 - W.map F (yL f3)), hK'⟩ : ↥(W.N T₂)) =
          ((PD.p : O) ^ e₂) • (⟨W.Q ^ (η + Bn) • w f3, hwK f3⟩ : ↥(W.N T₂)) -
            ⟨W.Q ^ (η + Bn) • W.map F (yL f3), hKy⟩ :=
        Subtype.ext (by
          show W.Q ^ (η + Bn) • (((PD.p : O) ^ e₂) • w f3 - W.map F (yL f3)) =
            ((PD.p : O) ^ e₂) • (W.Q ^ (η + Bn) • w f3) - W.Q ^ (η + Bn) • W.map F (yL f3)
          rw [smul_sub, osmul_comm W T₂])
      rw [e1, map_sub, levN_osmul W T₂ c ζ₀, hde f3, hlevy, smulS_sub (LB_smul (LB_mono hmd hMd) _) hLBy,
        smulS_smul (LB_mono hmd hMd), map_pow, map_natCast]
    have hFil : ∀ i : ℤ, ((((PD.p : LL) ^ e₂) • d f3 - ddy) i) ∈ Formalism.MainNotions.WachCoordinates.FilLev W T₂ c 0 (-i) := by
      intro i
      have hddyi : ddy i = ∑ k, algebraMap O LL (bF.repr f3 k) • dk k i := by
        simp only [hddy, Finset.sum_apply, Pi.smul_apply]
      simp only [Pi.sub_apply, Pi.smul_apply]
      by_cases hi0 : i = 0
      · subst hi0
        have hz : ψ4 f3 = 0 := (mem_zeroSub_coe F3 ψ4 hψ4 f3).1 f.2
        have hz' : (PD.p : LL) ^ e₂ • d f3 0 - (PD.p : LL) ^ κ •
            ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ellF f3)) ∈ F0 :=
          (Submodule.Quotient.mk_eq_zero F0).1 hz
        have hd0 : ddy 0 = (PD.p : LL) ^ κ •
            ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (ellF f3)) := by
          rw [hddyi]
          simp only [hellFdef, map_sum, map_smul, Finset.smul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [(hdkP k).2.1, smul_comm]
        rw [hd0, neg_zero]
        exact hz'
      · by_cases hiB : i < (Bn : ℤ)
        · have h0 : ddy i = 0 := by
            rw [hddyi]
            exact Finset.sum_eq_zero fun k _ => by rw [(hdkP k).1 i hiB hi0, smul_zero]
          rw [h0, sub_zero]
          exact Submodule.smul_mem _ _ (hdF f3 i hi0)
        · have hD : ddy i ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ c := by
            rw [hddyi]
            exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ((hdkP k).2.2 i)
          exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (hdF f3 i hi0))
            (hlow i (by omega) hD)
    exact ⟨mem_of_exp W T₂ hs hR hMC hT₂ c ζ₀ hTr u₀ hu₀ hw'D.1 hw'D.2 hK'
      ⟨M, LB_sub (LB_smul (LB_mono hmd hMd) _) hLBy⟩ hlev' hFil, hw'D⟩

end Pass4

end Formalism.MainNotions.N.Pv.LocalLengthBound
