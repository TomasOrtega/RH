import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsXPowMul

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Div2

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

/- English proof (translation)
Take `⟨w, u, hu, rfl⟩` from `exists_X_pow_mul f hf`. Use `set e' : ℤ → V := fun k => e (k + w) with he'`. Establish `hLB' : LB (m - w) e'` using `fun k hk => he _ (by omega)`. Use `⟨m - w, smulS u⁻¹ e', LB_smulS hLB' _, ?_, smulS_mem hLB' D (fun k => hD _) _⟩` and prove the remaining obligations. Rewrite using `[smulS_mul (LB_smulS hLB' _), ← smulS_mul hLB', PowerSeries.mul_inv_cancel _ hu, smulS_one hLB', smulS_X_pow hLB']`.

Use function extensionality and compare the values at `k`. Simplify using `[he']`.
-/
theorem smulS_div_mem {m : ℤ} {e : ℤ → V} (he : LB m e) (D : Submodule LL V) (hD : ∀ k, e k ∈ D)
    (f : PowerSeries LL) (hf : f ≠ 0) :
    ∃ (m' : ℤ) (d : ℤ → V), LB m' d ∧ smulS f d = e ∧ ∀ k, d k ∈ D := by
  obtain ⟨w, u, hu, rfl⟩ := exists_X_pow_mul f hf
  set e' : ℤ → V := fun k => e (k + w) with he'
  have hLB' : LB (m - w) e' := fun k hk => he _ (by omega)
  refine ⟨m - w, smulS u⁻¹ e', LB_smulS hLB' _, ?_, smulS_mem hLB' D (fun k => hD _) _⟩
  rw [smulS_mul (LB_smulS hLB' _), ← smulS_mul hLB', PowerSeries.mul_inv_cancel _ hu,
    smulS_one hLB', smulS_X_pow hLB']
  funext k
  simp [he']

/- English proof (translation)
Establish `hf' : LB m (fun j => Φ (f j))` using `fun j hj => by simp [hf j hj]`. Take `⟨N, hN⟩ : ∃ N : ℕ, k - m < N` from `⟨Int.toNat (k - m) + 1, by have := Int.self_le_toNat (k - m); push_cast; omega⟩`. Rewrite using `[smulS_eq_sum hf g k N hN, smulS_eq_sum hf' g k N hN, map_sum]`. Simplify using `[map_smul]`.
-/
theorem smulS_linMap {V' : Type} [AddCommGroup V'] [Module LL V'] (Φ : V →ₗ[LL] V') {m : ℤ}
    {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) (k : ℤ) :
    Φ (smulS g f k) = smulS g (fun j => Φ (f j)) k := by
  have hf' : LB m (fun j => Φ (f j)) := fun j hj => by simp [hf j hj]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k - m < N :=
    ⟨Int.toNat (k - m) + 1, by have := Int.self_le_toNat (k - m); push_cast; omega⟩
  rw [smulS_eq_sum hf g k N hN, smulS_eq_sum hf' g k N hN, map_sum]
  simp [map_smul]

end Div2

section Rules

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

/- English proof (translation)
Use function extensionality and compare the values at `k`. Rewrite using `[W.levN_smul]`. Both sides reduce to the same expression.
-/
theorem levN_smulS (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(W.N T)) :
    W.levN T i ζ (a • x) = smulS (W.lev i ζ a) (W.levN T i ζ x) := by
  funext k
  rw [W.levN_smul]
  rfl

/- English proof (translation)
Take `⟨⟨m, hm⟩, a, ha, hla, he⟩` from `hd`. Take `⟨⟨m', hm'⟩, a', ha', hla', he'⟩` from `hd'`. Establish `hdl : LB (min m m') d` using `fun k hk => hm k (by omega)`. Establish `hdl' : LB (min m m') d'` using `fun k hk => hm' k (by omega)`. Establish `hlev : W.levN T i ζ ⟨a • x, ha⟩ = smulS (W.lev i ζ a) d` using `funext he`.

Establish `hlev' : W.levN T i ζ ⟨a' • x, ha'⟩ = smulS (W.lev i ζ a') d'` using `funext he'`. Establish `e : a' • (⟨a • x, ha⟩ : ↥(W.N T)) = a • (⟨a' • x, ha'⟩ : ↥(W.N T))` using `Subtype.ext (by simp only [SetLike.val_smul]; rw [smul_smul, smul_smul, mul_comm])`. Establish `h` using `congrArg (W.levN T i ζ) e`. Rewrite `h` using `[levN_smulS, levN_smulS, hlev, hlev', ← smulS_mul hdl, ← smulS_mul hdl', mul_comm]`. Conclude with `smulS_inj hdl hdl' _ (mul_ne_zero hla hla') h`.
-/
theorem isExp_unique (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) {x : W.DD T}
    {d d' : ℤ → T.V ⊗[Qp] BdR} (hd : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d)
    (hd' : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d') : d = d' := by
  obtain ⟨⟨m, hm⟩, a, ha, hla, he⟩ := hd
  obtain ⟨⟨m', hm'⟩, a', ha', hla', he'⟩ := hd'
  have hdl : LB (min m m') d := fun k hk => hm k (by omega)
  have hdl' : LB (min m m') d' := fun k hk => hm' k (by omega)
  have hlev : W.levN T i ζ ⟨a • x, ha⟩ = smulS (W.lev i ζ a) d := funext he
  have hlev' : W.levN T i ζ ⟨a' • x, ha'⟩ = smulS (W.lev i ζ a') d' := funext he'
  have e : a' • (⟨a • x, ha⟩ : ↥(W.N T)) = a • (⟨a' • x, ha'⟩ : ↥(W.N T)) :=
    Subtype.ext (by simp only [SetLike.val_smul]; rw [smul_smul, smul_smul, mul_comm])
  have h := congrArg (W.levN T i ζ) e
  rw [levN_smulS, levN_smulS, hlev, hlev', ← smulS_mul hdl, ← smulS_mul hdl', mul_comm] at h
  exact smulS_inj hdl hdl' _ (mul_ne_zero hla hla') h

/- English proof (translation)
Introduce `hA T hT i ζ hζ`. Establish `hLv : ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ x k ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i` using `fun x k => by`. Use `(h4 T hT i 0 ζ (by rwa [zero_add, pow_one])).1 x k` as an intermediate fact. Rewrite `this` using `[Formalism.MainNotions.UnusedSlot80.LevR.filLev_zero]`. Conclude with `(Submodule.mem_inf.1 this).1`.

Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x a ha hla`. Take `⟨m, hm⟩` from `W.levN_supp T i ζ ⟨a • x, ha⟩`. Take `⟨m', d, hd, hde⟩` from `smulS_div (m := m) hm _ hla`. Establish `hE : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d` using `⟨⟨m', hd⟩, a, ha, hla, fun k => (congrFun hde k).symm⟩`.

Conclude with `⟨d, hE, fun d' hd' => isExp_unique W T i ζ hd' hE⟩`. Introduce `x d _ hx k`. Take `⟨⟨m, hm⟩, a, ha, hla, he⟩` from `hx`. Take `⟨m₀, hm₀⟩` from `W.levN_supp T i ζ ⟨a • x, ha⟩`. Take `⟨m', d₀, hd₀, hde₀, hmem⟩` from `smulS_div_mem (m := m₀) hm₀ (Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i) (fun k => hLv _ k) _ hla`.

Establish `hE₀ : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d₀` using `⟨⟨m', hd₀⟩, a, ha, hla, fun k => (congrFun hde₀ k).symm⟩`. Rewrite using `[isExp_unique W T i ζ ⟨⟨m, hm⟩, a, ha, hla, he⟩ hE₀]`. Conclude with `hmem k`. Introduce and unpack `x y d e ⟨⟨m, hm⟩, a, ha, hla, hd⟩ ⟨⟨m', hm'⟩, b, hb, hlb, he⟩`. Establish `hdl : LB (min m m') d` using `fun k hk => hm k (by omega)`.

Establish `hel : LB (min m m') e` using `fun k hk => hm' k (by omega)`. Establish `hmem : (a * b) • (x + y) ∈ W.N T`. Rewrite using `[smul_add, mul_comm, mul_smul, mul_comm, mul_smul]`. Conclude with `(W.N T).add_mem ((W.N T).smul_mem b ha) ((W.N T).smul_mem a hb)`. Use `⟨⟨min m m', LB_add hdl hel⟩, a * b, hmem, by rw [map_mul]; exact mul_ne_zero hla hlb, fun k => ?_⟩` and prove the remaining obligations.

Establish `e1 : (⟨(a * b) • (x + y), hmem⟩ : ↥(W.N T)) = b • (⟨a • x, ha⟩ : ↥(W.N T)) + a • (⟨b • y, hb⟩ : ↥(W.N T))` using `Subtype.ext (by`. Simplify using `only [Submodule.coe_add, SetLike.val_smul]`. Rewrite using `[smul_add, smul_smul, smul_smul, mul_comm b a])`. Rewrite using `[e1, map_add, Pi.add_apply, levN_smulS, levN_smulS, funext hd, funext he]`. Use `show smulS (W.lev i ζ b) (smulS (W.lev i ζ a) d) k + smulS (W.lev i ζ a) (smulS (W.lev i ζ b) e) k = smulS (W.lev i ζ (a * b)) (d + e) k`.

Rewrite using `[map_mul, smulS_add hdl hel, ← smulS_mul hdl, ← smulS_mul hel, mul_comm (W.lev i ζ b)]`. Both sides reduce to the same expression. Introduce and unpack `c x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩`. Establish `hmem : a • (c • x) ∈ W.N T`. Rewrite using `[smul_comm]`.

Conclude with `(W.N T).smul_of_tower_mem c ha`. Use `⟨⟨m, fun k hk => by simp [hm k hk]⟩, a, hmem, hla, fun k => ?_⟩` and prove the remaining obligations. Establish `e1 : (⟨a • (c • x), hmem⟩ : ↥(W.N T)) = (algebraMap O (LetA O n) c) • (⟨a • x, ha⟩ : ↥(W.N T))` using `Subtype.ext (by`. Simplify using `only [SetLike.val_smul]`. Rewrite using `[algebraMap_smul, smul_comm])`.

Rewrite using `[e1, levN_smulS, funext hd, AlgHom.commutes, PowerSeries.algebraMap_apply]`. Use `show smulS (PowerSeries.C (algebraMap O LL c)) (smulS (W.lev i ζ a) d) k = smulS (W.lev i ζ a) (fun k => algebraMap O LL c • d k) k`. Rewrite using `[smulS_C (LB_smulS hm _)]`. Establish `e2 : (fun k => algebraMap O LL c • d k) = algebraMap O LL c • d` using `rfl`. Rewrite using `[e2, smulS_smul hm]`.

Introduce and unpack `a' x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩`. Establish `hmem : a • (a' • x) ∈ W.N T`. Rewrite using `[smul_comm]`. Conclude with `(W.N T).smul_mem a' ha`. Use `⟨⟨m, LB_smulS hm _⟩, a, hmem, hla, fun k => ?_⟩` and prove the remaining obligations.

Establish `e1 : (⟨a • (a' • x), hmem⟩ : ↥(W.N T)) = a' • (⟨a • x, ha⟩ : ↥(W.N T))` using `Subtype.ext (by simp only [SetLike.val_smul]; rw [smul_comm])`. Rewrite using `[e1, levN_smulS, funext hd]`. Use `show smulS (W.lev i ζ a') (smulS (W.lev i ζ a) d) k = smulS (W.lev i ζ a) (smulS (W.lev i ζ a') d) k`. Rewrite using `[smulS_comm hm]`. Introduce and unpack `x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩`.

Establish `hχ : algebraMap O LL (W.χΓ W.gam : O) ≠ 0` using `((Units.isUnit (W.χΓ W.gam)).map (algebraMap O LL)).ne_zero`. Establish `hγN' : W.γ T (a • x) ∈ W.N T` using `W.N_Γ T W.gam _ ha`. Establish `hmem : W.γA W.gam a • W.γ T x ∈ W.N T`. Establish `h` using `hγN'`. Express the relevant statement in the definitionally equal form `W.γD T W.gam (a • x) ∈ W.N T at h`.

Rewrite `h` using `[RL.γD_smulA]`. Conclude with `h`. Use `⟨⟨m, LB_resc hm _⟩, W.γA W.gam a, hmem, ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[hA' i ζ hζ a]`. Introduce `h0`.

Conclude with `hla (PowerSeries.rescale_injective hχ (h0.trans (map_zero _).symm))`. Establish `e1 : (⟨W.γA W.gam a • W.γ T x, hmem⟩ : ↥(W.N T)) = ⟨W.γ T ((⟨a • x, ha⟩ : ↥(W.N T)) : W.DD T), hγN'⟩` using `Subtype.ext (RL.γD_smulA W T W.gam a x).symm`. Rewrite using `[e1, hN T hT i ζ hζ ⟨a • x, ha⟩ hγN' k, funext hd, hA' i ζ hζ a]`. Use `show algebraMap O LL (W.χΓ W.gam : O) ^ k • smulS (W.lev i ζ a) d k = smulS (PowerSeries.rescale (algebraMap O LL (W.χΓ W.gam : O)) (W.lev i ζ a)) (resc (algebraMap O LL (W.χΓ W.gam : O)) d) k`. Rewrite using `[smulS_rescale hm _ hχ]`.

Both sides reduce to the same expression. Introduce and unpack `T' F hT' x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩`. Establish `hmem : a • W.map F x ∈ W.N T'`. Rewrite using `[← RL.map_smulA]`. Conclude with `W.map_N F hT hT' _ ha`.

Use `⟨⟨m, fun k hk => by simp [hm k hk]⟩, a, hmem, hla, fun k => ?_⟩` and prove the remaining obligations. Establish `e1 : (⟨a • W.map F x, hmem⟩ : ↥(W.N T')) = ⟨W.map F ((⟨a • x, ha⟩ : ↥(W.N T)) : W.DD T), by rw [← RL.map_smulA] at hmem; exact hmem⟩` using `Subtype.ext (RL.map_smulA W F a x).symm`. Rewrite using `[e1, W.levN_map F hT hT' i ζ, hd]`. Conclude with `smulS_linMap _ hm _ k`.
-/
theorem expRules_of (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (hN : GamN W) (hA' : GamA W) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W := by
  intro hA T hT i ζ hζ
  have hLv : ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ x k ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i := fun x k => by
    have := (h4 T hT i 0 ζ (by rwa [zero_add, pow_one])).1 x k
    rw [Formalism.MainNotions.UnusedSlot80.LevR.filLev_zero] at this
    exact (Submodule.mem_inf.1 this).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x a ha hla
    obtain ⟨m, hm⟩ := W.levN_supp T i ζ ⟨a • x, ha⟩
    obtain ⟨m', d, hd, hde⟩ := smulS_div (m := m) hm _ hla
    have hE : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d :=
      ⟨⟨m', hd⟩, a, ha, hla, fun k => (congrFun hde k).symm⟩
    exact ⟨d, hE, fun d' hd' => isExp_unique W T i ζ hd' hE⟩
  ·
    intro x d _ hx k
    obtain ⟨⟨m, hm⟩, a, ha, hla, he⟩ := hx
    obtain ⟨m₀, hm₀⟩ := W.levN_supp T i ζ ⟨a • x, ha⟩
    obtain ⟨m', d₀, hd₀, hde₀, hmem⟩ := smulS_div_mem (m := m₀) hm₀ (Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i)
      (fun k => hLv _ k) _ hla
    have hE₀ : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d₀ :=
      ⟨⟨m', hd₀⟩, a, ha, hla, fun k => (congrFun hde₀ k).symm⟩
    rw [isExp_unique W T i ζ ⟨⟨m, hm⟩, a, ha, hla, he⟩ hE₀]
    exact hmem k
  ·
    rintro x y d e ⟨⟨m, hm⟩, a, ha, hla, hd⟩ ⟨⟨m', hm'⟩, b, hb, hlb, he⟩
    have hdl : LB (min m m') d := fun k hk => hm k (by omega)
    have hel : LB (min m m') e := fun k hk => hm' k (by omega)
    have hmem : (a * b) • (x + y) ∈ W.N T := by
      rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
      exact (W.N T).add_mem ((W.N T).smul_mem b ha) ((W.N T).smul_mem a hb)
    refine ⟨⟨min m m', LB_add hdl hel⟩, a * b, hmem, by rw [map_mul]; exact mul_ne_zero hla hlb,
      fun k => ?_⟩
    have e1 : (⟨(a * b) • (x + y), hmem⟩ : ↥(W.N T)) =
        b • (⟨a • x, ha⟩ : ↥(W.N T)) + a • (⟨b • y, hb⟩ : ↥(W.N T)) :=
      Subtype.ext (by
        simp only [Submodule.coe_add, SetLike.val_smul]
        rw [smul_add, smul_smul, smul_smul, mul_comm b a])
    rw [e1, map_add, Pi.add_apply, levN_smulS, levN_smulS, funext hd, funext he]
    show smulS (W.lev i ζ b) (smulS (W.lev i ζ a) d) k + smulS (W.lev i ζ a) (smulS (W.lev i ζ b) e) k =
      smulS (W.lev i ζ (a * b)) (d + e) k
    rw [map_mul, smulS_add hdl hel, ← smulS_mul hdl, ← smulS_mul hel, mul_comm (W.lev i ζ b)]
    rfl
  ·
    rintro c x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hmem : a • (c • x) ∈ W.N T := by
      rw [smul_comm]; exact (W.N T).smul_of_tower_mem c ha
    refine ⟨⟨m, fun k hk => by simp [hm k hk]⟩, a, hmem, hla, fun k => ?_⟩
    have e1 : (⟨a • (c • x), hmem⟩ : ↥(W.N T)) =
        (algebraMap O (LetA O n) c) • (⟨a • x, ha⟩ : ↥(W.N T)) :=
      Subtype.ext (by
        simp only [SetLike.val_smul]
        rw [algebraMap_smul, smul_comm])
    rw [e1, levN_smulS, funext hd, AlgHom.commutes, PowerSeries.algebraMap_apply]
    show smulS (PowerSeries.C (algebraMap O LL c)) (smulS (W.lev i ζ a) d) k =
      smulS (W.lev i ζ a) (fun k => algebraMap O LL c • d k) k
    rw [smulS_C (LB_smulS hm _)]
    have e2 : (fun k => algebraMap O LL c • d k) = algebraMap O LL c • d := rfl
    rw [e2, smulS_smul hm]
  ·
    rintro a' x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hmem : a • (a' • x) ∈ W.N T := by
      rw [smul_comm]; exact (W.N T).smul_mem a' ha
    refine ⟨⟨m, LB_smulS hm _⟩, a, hmem, hla, fun k => ?_⟩
    have e1 : (⟨a • (a' • x), hmem⟩ : ↥(W.N T)) = a' • (⟨a • x, ha⟩ : ↥(W.N T)) :=
      Subtype.ext (by simp only [SetLike.val_smul]; rw [smul_comm])
    rw [e1, levN_smulS, funext hd]
    show smulS (W.lev i ζ a') (smulS (W.lev i ζ a) d) k = smulS (W.lev i ζ a) (smulS (W.lev i ζ a') d) k
    rw [smulS_comm hm]
  ·
    rintro x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hχ : algebraMap O LL (W.χΓ W.gam : O) ≠ 0 :=
      ((Units.isUnit (W.χΓ W.gam)).map (algebraMap O LL)).ne_zero
    have hγN' : W.γ T (a • x) ∈ W.N T := W.N_Γ T W.gam _ ha
    have hmem : W.γA W.gam a • W.γ T x ∈ W.N T := by
      have h := hγN'
      change W.γD T W.gam (a • x) ∈ W.N T at h
      rw [RL.γD_smulA] at h
      exact h
    refine ⟨⟨m, LB_resc hm _⟩, W.γA W.gam a, hmem, ?_, fun k => ?_⟩
    · rw [hA' i ζ hζ a]
      intro h0
      exact hla (PowerSeries.rescale_injective hχ (h0.trans (map_zero _).symm))
    · have e1 : (⟨W.γA W.gam a • W.γ T x, hmem⟩ : ↥(W.N T)) =
          ⟨W.γ T ((⟨a • x, ha⟩ : ↥(W.N T)) : W.DD T), hγN'⟩ :=
        Subtype.ext (RL.γD_smulA W T W.gam a x).symm
      rw [e1, hN T hT i ζ hζ ⟨a • x, ha⟩ hγN' k, funext hd, hA' i ζ hζ a]
      show algebraMap O LL (W.χΓ W.gam : O) ^ k • smulS (W.lev i ζ a) d k =
        smulS (PowerSeries.rescale (algebraMap O LL (W.χΓ W.gam : O)) (W.lev i ζ a))
          (resc (algebraMap O LL (W.χΓ W.gam : O)) d) k
      rw [smulS_rescale hm _ hχ]
      rfl
  ·
    rintro T' F hT' x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hmem : a • W.map F x ∈ W.N T' := by
      rw [← RL.map_smulA]; exact W.map_N F hT hT' _ ha
    refine ⟨⟨m, fun k hk => by simp [hm k hk]⟩, a, hmem, hla, fun k => ?_⟩
    have e1 : (⟨a • W.map F x, hmem⟩ : ↥(W.N T')) =
        ⟨W.map F ((⟨a • x, ha⟩ : ↥(W.N T)) : W.DD T), by rw [← RL.map_smulA] at hmem; exact hmem⟩ :=
      Subtype.ext (RL.map_smulA W F a x).symm
    rw [e1, W.levN_map F hT hT' i ζ, hd]
    exact smulS_linMap _ hm _ k

end Rules

end Formalism.MainNotions.N.Pv.LocalLengthBound
