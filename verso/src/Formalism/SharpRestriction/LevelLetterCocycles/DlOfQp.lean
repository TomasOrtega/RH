import Formalism.SharpRestriction.LevelLetterCocycles.JumpsInLetterOfEvenIndex
import Formalism.SharpRestriction.LevelLetterCocycles.DvOZeroHigh
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsXPowMul
import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.GM

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD
  Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

/- English proof (translation)
Introduce `a b hab`. Conclude with `Submodule.map_mono (Submodule.map_mono (inf_le_inf_right _ fun x hx => Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hab hx))`.
-/
theorem filLev_anti (T : LocLat G Qp LL O) (i : ZMod n) :
    Antitone fun a : ℤ => Formalism.MainNotions.WachCoordinates.FilLev W T i 0 a := by
  intro a b hab
  exact Submodule.map_mono (Submodule.map_mono
    (inf_le_inf_right _ fun x hx => Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hab hx))

/- English proof (translation)
Introduce `z hz`. Take `⟨x, hx, rfl⟩` from `hz`. Take `⟨τ, hτ, hover⟩` from `Formalism.MainNotions.UnusedSlot80.LevC.tau_over W hbij i`. Establish `h1` using `Formalism.MainNotions.UnusedSlot80.LevC.fil_low W T i τ hover hbij.2 H (hJ τ hτ) hx`. Establish `h2` using `Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ ha h1`.

Use `⟨x, ⟨x, ⟨h2, by simpa using hx⟩, by simp⟩, rfl⟩` and prove the remaining obligations.
-/
theorem ιDi_le_fil (hbij : Function.Bijective (algebraMap K₀ K)) (T : LocLat G Qp LL O) (i : ZMod n)
    (H : ℕ) (hJ : ∀ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i → ∀ a, IsJumpV PD T.ρ τ a → -(H : ℤ) ≤ a)
    (a : ℤ) (ha : a ≤ -(H : ℤ)) : Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i ≤ Formalism.MainNotions.WachCoordinates.FilLev W T i 0 a := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨τ, hτ, hover⟩ := Formalism.MainNotions.UnusedSlot80.LevC.tau_over W hbij i
  have h1 := Formalism.MainNotions.UnusedSlot80.LevC.fil_low W T i τ hover hbij.2 H (hJ τ hτ) hx
  have h2 := Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ ha h1
  refine ⟨x, ⟨x, ⟨h2, by simpa using hx⟩, by simp⟩, rfl⟩

/- English proof (translation)
Unfold `gE`. Rewrite using `[← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ c), smul_smul, map_pow, ← mul_pow, Ring.mul_inverse_cancel _ hq, one_pow, one_smul]`.
-/
theorem qp_smul_gE (hq : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (T : LocLat G Qp LL O)
    (h c : ℕ) {r : ℕ} (e' : Fin r → W.DD T) (Z : Matrix (Fin r) (Fin r) (PowerSeries O)) (k : Fin r) :
    Formalism.MainNotions.LiftingTheory.qp W ^ c • gE W T h c e' Z k = Formalism.MainNotions.LiftingTheory.qp W ^ h • ftE W T e' Z k := by
  unfold gE
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ c), smul_smul, map_pow, ← mul_pow,
    Ring.mul_inverse_cancel _ hq, one_pow, one_smul]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_pow, Ring.inverse_mul_cancel _ hq, one_pow, one_smul]`. Use `_ = (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) ^ c • (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ c) • z) := by rw [smul_smul, map_pow]`. Use `_ = 0 := by rw [algebraMap_smul, hz, smul_zero]`.
-/
theorem qp_pow_inj (hq : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (T : LocLat G Qp LL O)
    (c : ℕ) (z : W.DD T) (hz : Formalism.MainNotions.LiftingTheory.qp W ^ c • z = 0) : z = 0 := by
  calc z = ((Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) ^ c *
        (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ c) • z := by
          rw [← mul_pow, Ring.inverse_mul_cancel _ hq, one_pow, one_smul]
    _ = (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) ^ c •
        (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ c) • z) := by rw [smul_smul, map_pow]
    _ = 0 := by rw [algebraMap_smul, hz, smul_zero]

/- English proof (translation)
The claim follows from `W.AΔ.add_mem (Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.uniformizer_mem_delta_invariants W) (W.AΔ.natCast_mem _)`.
-/
theorem qp_mem_AΔ : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ :=
  W.AΔ.add_mem (Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.uniformizer_mem_delta_invariants W) (W.AΔ.natCast_mem _)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Apply `sub_eq_zero.1` to reduce the goal to its premises. Apply `qp_pow_inj W hq T c` to reduce the goal to its premises. Rewrite using `[smul_sub, smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ c) (letE i : LetA O n) g, hgy, hy.1, sub_self]`. Introduce `δ hδ`.

Apply `sub_eq_zero.1` to reduce the goal to its premises. Apply `qp_pow_inj W hq T c` to reduce the goal to its premises. Establish `hA : W.γA δ (Formalism.MainNotions.LiftingTheory.qp W ^ c) = Formalism.MainNotions.LiftingTheory.qp W ^ c` using `W.AΔ.pow_mem (qp_mem_AΔ W) c δ hδ`. Establish `e` using `Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γD_smulA W T δ (Formalism.MainNotions.LiftingTheory.qp W ^ c) g`. Rewrite `e` using `[hA, hgy, hy.2 δ hδ]`.

Rewrite using `[smul_sub, ← e, hgy, sub_self]`.
-/
theorem dl_of_qp (hq : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (T : LocLat G Qp LL O)
    (i : ZMod n) (c : ℕ) (g y : W.DD T) (hgy : Formalism.MainNotions.LiftingTheory.qp W ^ c • g = y)
    (hy : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i y) : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i g := by
  constructor
  · apply sub_eq_zero.1
    apply qp_pow_inj W hq T c
    rw [smul_sub, smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ c) (letE i : LetA O n) g, hgy, hy.1, sub_self]
  · intro δ hδ
    apply sub_eq_zero.1
    apply qp_pow_inj W hq T c
    have hA : W.γA δ (Formalism.MainNotions.LiftingTheory.qp W ^ c) = Formalism.MainNotions.LiftingTheory.qp W ^ c :=
      W.AΔ.pow_mem (qp_mem_AΔ W) c δ hδ
    have e := Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γD_smulA W T δ (Formalism.MainNotions.LiftingTheory.qp W ^ c) g
    rw [hA, hgy, hy.2 δ hδ] at e
    rw [smul_sub, ← e, hgy, sub_self]

/- English proof (translation)
Establish `hfin1 : finrank K₀ K = 1`. Use `(LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq` as an intermediate fact. Rewrite `this` using `[Module.finrank_self]`. Conclude with `this.symm`. Take `⟨-, -, h9'⟩` from `h9 T hT hA.2.1 hA.2.2`.

Take `⟨hring, -⟩` from `h9' hfin1`. Conclude with `hring`.
-/
theorem ring_clauses_at_uniformizer (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.Ring9 W := by
  have hfin1 : finrank K₀ K = 1 := by
    have := (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq
    rw [Module.finrank_self] at this
    exact this.symm
  obtain ⟨-, -, h9'⟩ := h9 T hT hA.2.1 hA.2.2
  obtain ⟨hring, -⟩ := h9' hfin1
  exact hring

/- English proof (translation)
Establish `hie : (i.val + d) % 2 = 0` using `(Finset.mem_filter.1 hi).2`. Establish `hCA : Formalism.MainNotions.LiftingTheory.CaseA W` using `hS.1`. Establish `hT : IsCrys PD T₂.ρ` using `hS.2.2.2.2.2.1.2.1`. Establish `hl11 : 11 ≤ PD.p` using `hS.2.1`. Take `⟨ζ, hζ⟩` from `hS.2.2.2.2.1`.

Take `⟨-, hπu, w, hw⟩` from `DetS.uniformizer_unit_and_q_factor W h9 hCA T₂ hT (by omega)`. Establish `hq` using `DetS.qp_unit W hπu`. Establish `hR9` using `ring_clauses_at_uniformizer W h9 hCA T₂ hT`. Take `⟨-, -, hmr', hwin, hfil, -⟩` from `id had`. Establish `hηb` using `Formalism.MainNotions.N.Pv.LocalLengthBound.rk_eta_lt W hS i`.

Use `set h : ℕ := b i + S with hhdef`. Use `set k : Fin (finrank LL T₂.V) := Fin.castLE hmr j with hkdef`. Use `set c : ℕ := ((h : ℤ) + u j).toNat with hcdef`. Establish `hc : (c : ℤ) = h + u j` using `Int.toNat_of_nonneg (by have := (hwin j).1; omega)`. Establish `hyN : Formalism.MainNotions.LiftingTheory.qp W ^ h • ftE W T₂ e' Z k ∈ NDl W T₂ i`.

Unfold `ftE`. Rewrite using `[Finset.smul_sum]`. Use `Submodule.sum_mem _ fun m₁ _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm, pow_one]`. Establish `hm` using `DetA.qpφ_mem W hE hC hQ h5 h9 hS i hie e' had.1 m₁`.

Establish `ha` using `Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_mem_invariants W hR9 (Z m₁ k)`. Use `⟨(W.N T₂).smul_mem _ hm.1, ?_, fun δ hδ => ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm (letE i : LetA O n), hm.2.1]`. Rewrite using `[Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γD_smulA W T₂ δ, ha δ hδ, hm.2.2 δ hδ]`. Establish `hgy` using `qp_smul_gE W hq T₂ h c e' Z k`.

Establish `hgDL` using `dl_of_qp W hq T₂ i c _ _ hgy hyN.2`. Take `⟨u0, hlq, hu0⟩` from `Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.lev_q_X_mul W i ζ hζ (by omega) (Formalism.MainNotions.N.Pv.LocalLengthBound.p_ne_zero_LL W)`. Use `set U : PowerSeries LL := W.lev i ζ ((↑w⁻¹ : (LetA O n)ˣ) : LetA O n) * u0 with hUdef`. Establish `hwq : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W) = PowerSeries.X * U`. Establish `e : Formalism.MainNotions.LiftingTheory.qp W = ((↑w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.q`.

Rewrite using `[hw, ← mul_assoc, Units.inv_mul, one_mul]`. Rewrite using `[e, map_mul, hlq, hUdef]`. Expand and normalize the polynomial expressions, which then agree. Establish `hU : PowerSeries.constantCoeff U ≠ 0`. Rewrite using `[hUdef, map_mul]`.

Use `mul_ne_zero ?_ hu0` and prove the remaining obligations. Conclude with `(PowerSeries.isUnit_iff_constantCoeff.1 ((Units.isUnit _).map (W.lev i ζ))).ne_zero`. Establish `hU0 : U ≠ 0` using `fun h0 => hU (by rw [h0, map_zero])`. Establish `hlevpow : ∀ t : ℕ, W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ t) = PowerSeries.X ^ t * U ^ t`. Introduce `t`.

Rewrite using `[map_pow, hwq, mul_pow]`. Establish `hlevne : ∀ t : ℕ, W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ t) ≠ 0`. Introduce `t`. Rewrite using `[hlevpow]`. Conclude with `mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (pow_ne_zero _ hU0)`.

Take `⟨hEx, hDi, -, -, hconv, -, -⟩` from `hRu hCA T₂ hT i ζ hζ`. Take `⟨df, hdf, -⟩` from `hEx (ftE W T₂ e' Z k) _ hyN.1 (hlevne h)`. Take `⟨dg, hdg, -⟩` from `hEx (gE W T₂ h c e' Z k) (Formalism.MainNotions.LiftingTheory.qp W ^ c) (by rw [hgy]; exact hyN.1) (hlevne c)`. Establish `hy1` using `hconv (Formalism.MainNotions.LiftingTheory.qp W ^ h) _ df hdf`. Establish `hy2` using `hconv (Formalism.MainNotions.LiftingTheory.qp W ^ c) _ dg hdg`.

Rewrite `hy2` using `[hgy]`. Establish `huniq` using `(hEx (Formalism.MainNotions.LiftingTheory.qp W ^ h • ftE W T₂ e' Z k) 1 (by rw [one_smul]; exact hyN.1) (by rw [map_one]; exact one_ne_zero)).unique hy2 hy1`. Take `⟨mg, hmg⟩` from `hdg.1`. Establish `hi1 : i - 1 + ((1 : ℕ) : ZMod n) = i` using `by push_cast; ring`. Establish `hZ` using `hZP.2 k ζ hζ df (by rw [hi1]; exact hdf)`.

Establish `hv : ιV PD (LL` using `LL) (V := T₂.V) ((φVB PD (LL := LL) (V := T₂.V))^[1] (W.cmp T₂ ⟨e' k, (had.1.1 k).1⟩)) ∈ Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 (u j) := by`. Rewrite using `[Function.iterate_one]`. Conclude with `hfil j _`. Use `set Fil : ℤ → Submodule LL (T₂.V ⊗[Qp] BdR) := fun a => Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 a with hFil`. Establish `hanti : Antitone Fil` using `filLev_anti W T₂ i`.

Establish `hLBf : Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB 0 df`. Introduce `t ht`. Rewrite using `[hZ t (by omega), if_neg (by omega)]`. Use `set Ff := Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS (U ^ h) df with hFf`. Use `set E := Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS (U ^ c) dg with hEdef`.

Establish `hF_mem : ∀ s : ℤ, s < ((h + η : ℕ) : ℤ) → Ff s ∈ Fil (u j)`. Introduce `s hs`. Rewrite using `[hFf, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_eq_sum hLBf (U ^ h) s (s.toNat + 1) (by have := Int.self_le_toNat s; omega)]`. Use `Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Rewrite using `[hZ _ (by omega)]`.

Use `split_ifs`. Conclude with `Submodule.smul_mem _ _ hv`. Conclude with `Submodule.zero_mem _`. Establish `hF_neg : ∀ s : ℤ, s < 0 → Ff s = 0` using `fun s hs => Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hLBf (U ^ h) s hs`. Establish `hEF : ∀ t : ℤ, E t = Ff (t + u j)`.

Introduce `t`. Establish `e1 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ c)) dg = fun s => E (s - c)`. Rewrite using `[hlevpow, Formalism.MainNotions.N.Pv.LocalLengthBound.conv_eq, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_mul hmg, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_X_pow (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hmg _)]`. Establish `e2 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ h)) df = fun s => Ff (s - h)`. Rewrite using `[hlevpow, Formalism.MainNotions.N.Pv.LocalLengthBound.conv_eq, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_mul hLBf, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_X_pow (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hLBf _)]`.

Establish `e3` using `congrFun huniq (t + c)`. Rewrite `e3` using `[e1, e2]`. Simplify using `only at e3`. Rewrite `e3` using `[show t + (c : ℤ) - c = t by ring, show t + (c : ℤ) - h = t + u j by omega]`. Conclude with `e3`.

Establish `hEDi : ∀ t, E t ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i` using `fun t => Formalism.MainNotions.N.Pv.LocalLengthBound.smulS_mem hmg _ (hDi _ dg hgDL hdg) (U ^ c) t`. Establish `hlow : ∀ a : ℤ, a ≤ -(h : ℤ) → Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i ≤ Fil a`. Introduce `a ha`. Use `ιDi_le_fil W hCA.1 T₂ i h (fun τ hτ a' ha' => ?_) a ha` and prove the remaining obligations. Establish `hw2` using `Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS i τ hτ a' ha'`.

Unfold `JumpWinS at hw2`. Rewrite `hw2` using `[if_pos hie]`. Simplify using `only [Set.mem_union, Set.mem_Icc] at hw2`. Rewrite using `[hhdef]`. Move the coercions through the operations in `at hw2 ⊢`.

Use linear arithmetic over natural numbers and integers. Establish `hDgE : Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.Dg Fil 0 E`. Introduce `t`. Distinguish the cases in `ht : t + u j < ((h + η : ℕ) : ℤ)`. Rewrite using `[hEF t]`.

Distinguish the cases in `h0 : t + u j < 0`. Rewrite using `[hF_neg _ h0]`. Conclude with `Submodule.zero_mem _`. Conclude with `hanti (show 0 - t ≤ u j by omega) (hF_mem _ ht)`. Conclude with `hlow (0 - t) (by have := (hwin j).2; push_cast at ht; omega) (hEDi t)`.

Establish `hUc : PowerSeries.constantCoeff (U ^ c) ≠ 0` using `by rw [map_pow]; exact pow_ne_zero _ hU`. Establish `hdg_eq : dg = Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS (U ^ c)⁻¹ E` using `(Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_inv hmg (U ^ c) hUc).symm`. Establish `hDg : Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.Dg Fil 0 dg`. Rewrite using `[hdg_eq]`. Conclude with `Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.Dg_smulS hanti (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hmg _) hDgE _`.

Establish `hcrit` using `(hEC hCA T₂ hT i ζ hζ _ dg hgDL hdg).1 ⟨c, by rw [hgy]; exact hyN.1⟩`. Use `⟨hcrit.2 fun t => ?_, hgDL⟩` and prove the remaining obligations. Use `hDg t` as an intermediate fact. Simplify `this` using `[hFil]`.
-/
theorem gE_mem (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W) (hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W)
    {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ}
    (hS : SetCS W d T₁ T₂ F b S η m) (i : ZMod n) (hi : i ∈ evens n d)
    (e' : Fin (finrank LL T₂.V) → W.DD T₂) (m' : ℕ) (u : Fin m' → ℤ)
    (had : AdaptData W T₂ i (b i + S) η m e' m' u) (σ : ℕ) (Z : Matrix _ _ (PowerSeries O))
    (hZP : ZProps W T₂ i (b i + S + η) σ e' had.1 Z) (j : Fin m') (hmr : m' ≤ finrank LL T₂.V) :
    gE W T₂ (b i + S) ((b i + S : ℕ) + u j).toNat e' Z (Fin.castLE hmr j) ∈ NDl W T₂ i := by
  have hie : (i.val + d) % 2 = 0 := (Finset.mem_filter.1 hi).2
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hT : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hl11 : 11 ≤ PD.p := hS.2.1
  obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
  obtain ⟨-, hπu, w, hw⟩ := DetS.uniformizer_unit_and_q_factor W h9 hCA T₂ hT (by omega)
  have hq := DetS.qp_unit W hπu
  have hR9 := ring_clauses_at_uniformizer W h9 hCA T₂ hT
  obtain ⟨-, -, hmr', hwin, hfil, -⟩ := id had
  have hηb := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_eta_lt W hS i
  set h : ℕ := b i + S with hhdef
  set k : Fin (finrank LL T₂.V) := Fin.castLE hmr j with hkdef
  set c : ℕ := ((h : ℤ) + u j).toNat with hcdef
  have hc : (c : ℤ) = h + u j := Int.toNat_of_nonneg (by have := (hwin j).1; omega)

  have hyN : Formalism.MainNotions.LiftingTheory.qp W ^ h • ftE W T₂ e' Z k ∈ NDl W T₂ i := by
    unfold ftE
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun m₁ _ => ?_
    rw [smul_comm, pow_one]
    have hm := DetA.qpφ_mem W hE hC hQ h5 h9 hS i hie e' had.1 m₁
    have ha := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_mem_invariants W hR9 (Z m₁ k)
    refine ⟨(W.N T₂).smul_mem _ hm.1, ?_, fun δ hδ => ?_⟩
    · rw [smul_comm (letE i : LetA O n), hm.2.1]
    · rw [Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γD_smulA W T₂ δ, ha δ hδ, hm.2.2 δ hδ]
  have hgy := qp_smul_gE W hq T₂ h c e' Z k
  have hgDL := dl_of_qp W hq T₂ i c _ _ hgy hyN.2

  obtain ⟨u0, hlq, hu0⟩ := Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.lev_q_X_mul W i ζ hζ (by omega)
    (Formalism.MainNotions.N.Pv.LocalLengthBound.p_ne_zero_LL W)
  set U : PowerSeries LL := W.lev i ζ ((↑w⁻¹ : (LetA O n)ˣ) : LetA O n) * u0 with hUdef
  have hwq : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W) = PowerSeries.X * U := by
    have e : Formalism.MainNotions.LiftingTheory.qp W = ((↑w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.q := by
      rw [hw, ← mul_assoc, Units.inv_mul, one_mul]
    rw [e, map_mul, hlq, hUdef]; ring
  have hU : PowerSeries.constantCoeff U ≠ 0 := by
    rw [hUdef, map_mul]
    refine mul_ne_zero ?_ hu0
    exact (PowerSeries.isUnit_iff_constantCoeff.1 ((Units.isUnit _).map (W.lev i ζ))).ne_zero
  have hU0 : U ≠ 0 := fun h0 => hU (by rw [h0, map_zero])
  have hlevpow : ∀ t : ℕ, W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ t) = PowerSeries.X ^ t * U ^ t := by
    intro t; rw [map_pow, hwq, mul_pow]
  have hlevne : ∀ t : ℕ, W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ t) ≠ 0 := by
    intro t; rw [hlevpow]; exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (pow_ne_zero _ hU0)

  obtain ⟨hEx, hDi, -, -, hconv, -, -⟩ := hRu hCA T₂ hT i ζ hζ
  obtain ⟨df, hdf, -⟩ := hEx (ftE W T₂ e' Z k) _ hyN.1 (hlevne h)
  obtain ⟨dg, hdg, -⟩ := hEx (gE W T₂ h c e' Z k) (Formalism.MainNotions.LiftingTheory.qp W ^ c) (by rw [hgy]; exact hyN.1)
    (hlevne c)
  have hy1 := hconv (Formalism.MainNotions.LiftingTheory.qp W ^ h) _ df hdf
  have hy2 := hconv (Formalism.MainNotions.LiftingTheory.qp W ^ c) _ dg hdg
  rw [hgy] at hy2
  have huniq := (hEx (Formalism.MainNotions.LiftingTheory.qp W ^ h • ftE W T₂ e' Z k) 1 (by rw [one_smul]; exact hyN.1)
    (by rw [map_one]; exact one_ne_zero)).unique hy2 hy1
  obtain ⟨mg, hmg⟩ := hdg.1
  have hi1 : i - 1 + ((1 : ℕ) : ZMod n) = i := by push_cast; ring
  have hZ := hZP.2 k ζ hζ df (by rw [hi1]; exact hdf)
  have hv : ιV PD (LL := LL) (V := T₂.V) ((φVB PD (LL := LL) (V := T₂.V))^[1]
      (W.cmp T₂ ⟨e' k, (had.1.1 k).1⟩)) ∈ Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 (u j) := by
    rw [Function.iterate_one]; exact hfil j _
  set Fil : ℤ → Submodule LL (T₂.V ⊗[Qp] BdR) := fun a => Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 a with hFil
  have hanti : Antitone Fil := filLev_anti W T₂ i
  have hLBf : Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB 0 df := by
    intro t ht
    rw [hZ t (by omega), if_neg (by omega)]
  set Ff := Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS (U ^ h) df with hFf
  set E := Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS (U ^ c) dg with hEdef
  have hF_mem : ∀ s : ℤ, s < ((h + η : ℕ) : ℤ) → Ff s ∈ Fil (u j) := by
    intro s hs
    rw [hFf, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_eq_sum hLBf (U ^ h) s (s.toNat + 1)
      (by have := Int.self_le_toNat s; omega)]
    refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
    rw [hZ _ (by omega)]
    split_ifs
    · exact Submodule.smul_mem _ _ hv
    · exact Submodule.zero_mem _
  have hF_neg : ∀ s : ℤ, s < 0 → Ff s = 0 := fun s hs =>
    Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hLBf (U ^ h) s hs
  have hEF : ∀ t : ℤ, E t = Ff (t + u j) := by
    intro t
    have e1 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ c)) dg = fun s => E (s - c) := by
      rw [hlevpow, Formalism.MainNotions.N.Pv.LocalLengthBound.conv_eq, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_mul hmg,
        Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_X_pow (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hmg _)]
    have e2 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ h)) df = fun s => Ff (s - h) := by
      rw [hlevpow, Formalism.MainNotions.N.Pv.LocalLengthBound.conv_eq, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_mul hLBf,
        Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_X_pow (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hLBf _)]
    have e3 := congrFun huniq (t + c)
    rw [e1, e2] at e3
    simp only at e3
    rw [show t + (c : ℤ) - c = t by ring, show t + (c : ℤ) - h = t + u j by omega] at e3
    exact e3
  have hEDi : ∀ t, E t ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i := fun t =>
    Formalism.MainNotions.N.Pv.LocalLengthBound.smulS_mem hmg _ (hDi _ dg hgDL hdg) (U ^ c) t
  have hlow : ∀ a : ℤ, a ≤ -(h : ℤ) → Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i ≤ Fil a := by
    intro a ha
    refine ιDi_le_fil W hCA.1 T₂ i h (fun τ hτ a' ha' => ?_) a ha
    have hw2 := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS i τ hτ a' ha'
    unfold JumpWinS at hw2
    rw [if_pos hie] at hw2
    simp only [Set.mem_union, Set.mem_Icc] at hw2
    rw [hhdef]; push_cast at hw2 ⊢
    omega
  have hDgE : Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.Dg Fil 0 E := by
    intro t
    by_cases ht : t + u j < ((h + η : ℕ) : ℤ)
    · rw [hEF t]
      by_cases h0 : t + u j < 0
      · rw [hF_neg _ h0]; exact Submodule.zero_mem _
      · exact hanti (show 0 - t ≤ u j by omega) (hF_mem _ ht)
    · exact hlow (0 - t) (by have := (hwin j).2; push_cast at ht; omega) (hEDi t)
  have hUc : PowerSeries.constantCoeff (U ^ c) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hU
  have hdg_eq : dg = Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS (U ^ c)⁻¹ E :=
    (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_inv hmg (U ^ c) hUc).symm
  have hDg : Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.Dg Fil 0 dg := by
    rw [hdg_eq]
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.Dg_smulS hanti (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hmg _) hDgE _
  have hcrit := (hEC hCA T₂ hT i ζ hζ _ dg hgDL hdg).1 ⟨c, by rw [hgy]; exact hyN.1⟩
  refine ⟨hcrit.2 fun t => ?_, hgDL⟩
  have := hDg t
  simpa [hFil] using this

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ hS i hi e' m' u had σ Z hZP j hmr` and use `gE_mem W hE hC hQ h5 h9 hRu hEC hS i hi e' m' u had σ Z hZP j hmr`.
-/
theorem gMem_of (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W) (hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W) : GMem W :=
  fun _ _ _ _ _ _ _ _ hS i hi e' m' u had σ Z hZP j hmr =>
    gE_mem W hE hC hQ h5 h9 hRu hEC hS i hi e' m' u had σ Z hZP j hmr

end Formalism.MainNotions.RamifiedCoefficientChains.S9.GM
