import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliaryNormPrimes
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobalAssemblyOfStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.GluingLemmasAndTheorems
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge

noncomputable section

namespace Formalism.MainNotions

open NumberField Formalism.BasicNotions Formalism.MainNotions.S.Lat Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section LinAlg

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

/- English proof (translation)
Simplify using `[orth, Submodule.mem_iInf]`.
-/
theorem mem_orth_iff (U : Submodule E S.V) (v : S.V) : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

/- English proof (translation)
Use `S.herm.eq x y` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `this.symm`.
-/
theorem hT_swap_zero {x y : S.V} (h : S.hT x y = 0) : S.hT y x = 0 := by
  have := S.herm.eq x y
  rw [h, map_zero] at this
  exact this.symm

/- English proof (translation)
Establish `h : F.X ≤ LinearMap.ker (S.hT.flip v)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Simplify using `using hv a`. Introduce `x hx`.

Simplify using `using h hx`.
-/
theorem hT_zero_of_mem_X (F : Formalism.MainNotions.S.FlagG S r T) {v : S.V} (hv : ∀ a, S.hT (F.e a) v = 0) :
    ∀ x ∈ F.X, S.hT x v = 0 := by
  have h : F.X ≤ LinearMap.ker (S.hT.flip v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    simpa using hv a
  intro x hx
  simpa using h hx

/- English proof (translation)
Establish `h : F.Xplus ≤ LinearMap.ker (S.hT.flip v)`. Use `sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Simplify using `using hv a`. Introduce `y hy`.

Rewrite `hy` using `[Set.mem_singleton_iff]`. Substitute `hy` using the available equality. Simplify using `using hz`. Introduce `x hx`. Simplify using `using h hx`.
-/
theorem hT_zero_of_mem_Xplus (F : Formalism.MainNotions.S.FlagG S r T) {v : S.V} (hv : ∀ a, S.hT (F.e a) v = 0)
    (hz : S.hT F.z v = 0) : ∀ x ∈ F.Xplus, S.hT x v = 0 := by
  have h : F.Xplus ≤ LinearMap.ker (S.hT.flip v) := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨a, rfl⟩
      simpa using hv a
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      simpa using hz
  intro x hx
  simpa using h hx

/- English proof (translation)
Use `Fin.lastCases ?_ (fun i => ?_) a` and prove the remaining obligations. Simplify using `only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Simplify using `only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]`. Conclude with `Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem fvec_mem_Xplus (F : Formalism.MainNotions.S.FlagG S r T) (a : Fin (r + 1)) : F.fvec a ∈ F.Xplus := by
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Introduce `hz`. Use `hT_zero_of_mem_X F (v := F.z) F.z_orth _ hz` as an intermediate fact. Rewrite `this` using `[F.z_norm]`. Conclude with `hT (neg_eq_zero.mp this)`.
-/
theorem z_notMem_X (F : Formalism.MainNotions.S.FlagG S r T) (hT : T ≠ 0) : F.z ∉ F.X := by
  intro hz
  have := hT_zero_of_mem_X F (v := F.z) F.z_orth _ hz
  rw [F.z_norm] at this
  exact hT (neg_eq_zero.mp this)

/- English proof (translation)
Establish `hind : LinearIndependent E F.fvec` using `LinearIndependent.finSnoc F.e_indep (z_notMem_X F hT)`. Set `ℓ : Fin (r + 1) → Module.Dual E S.V` to `fun a => S.hT (F.fvec a)`. Establish `hℓ : LinearIndependent E ℓ`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc a`.

Establish `h1 : S.hT (∑ a, star (c a) • F.fvec a) = 0`. Rewrite using `[map_sum, ← hc]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, starRingEnd_apply, star_star]`. Establish `h2 : ∑ a, star (c a) • F.fvec a = 0` using `S.nondeg.1 _ (fun y => by rw [h1]; rfl)`.

Establish `h3` using `Fintype.linearIndependent_iff.1 hind _ h2 a`. Simplify using `using h3`. Establish `hΦ : finrank E (Submodule.span E (Set.range ℓ)) = r + 1`. Rewrite using `[finrank_span_eq_card hℓ]`. Simplify using the standard rewrite rules.

Establish `hco : (Submodule.span E (Set.range ℓ)).dualCoannihilator = orth S F.Xplus`. Use extensionality with `v`. Rewrite using `[Submodule.mem_dualCoannihilator, mem_orth_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `hT_zero_of_mem_Xplus F (fun a => ?_) ?_` and prove the remaining obligations. Use `h (ℓ a.castSucc) (Submodule.subset_span ⟨_, rfl⟩)` as an intermediate fact. Simplify `this` using `[ℓ, Formalism.MainNotions.S.FlagG.fvec]`. Use `h (ℓ (Fin.last r)) (Submodule.subset_span ⟨_, rfl⟩)` as an intermediate fact. Simplify `this` using `[ℓ, Formalism.MainNotions.S.FlagG.fvec]`.

Introduce `h φ hφ`. Use `Submodule.span_induction (p := fun φ _ => φ v = 0) ?_ ?_ ?_ ?_ hφ` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `h _ (fvec_mem_Xplus F a)`. Simplify using the standard rewrite rules.

Introduce `x y _ _ hx hy`. Simplify using `[hx, hy]`. Introduce `c x _ hx`. Simplify using `[hx]`. Use `Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span E (Set.range ℓ))` as an intermediate fact.

Rewrite `this` using `[hΦ, hco]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_orth_Xplus (F : Formalism.MainNotions.S.FlagG S r T) (hT : T ≠ 0) :
    finrank E (orth S F.Xplus) + (r + 1) = finrank E S.V := by
  classical
  have hind : LinearIndependent E F.fvec := LinearIndependent.finSnoc F.e_indep (z_notMem_X F hT)
  let ℓ : Fin (r + 1) → Module.Dual E S.V := fun a => S.hT (F.fvec a)
  have hℓ : LinearIndependent E ℓ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc a
    have h1 : S.hT (∑ a, star (c a) • F.fvec a) = 0 := by
      rw [map_sum, ← hc]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_smulₛₗ, starRingEnd_apply, star_star]
    have h2 : ∑ a, star (c a) • F.fvec a = 0 := S.nondeg.1 _ (fun y => by rw [h1]; rfl)
    have h3 := Fintype.linearIndependent_iff.1 hind _ h2 a
    simpa using h3
  have hΦ : finrank E (Submodule.span E (Set.range ℓ)) = r + 1 := by
    rw [finrank_span_eq_card hℓ]; simp
  have hco : (Submodule.span E (Set.range ℓ)).dualCoannihilator = orth S F.Xplus := by
    ext v
    rw [Submodule.mem_dualCoannihilator, mem_orth_iff]
    constructor
    · intro h
      refine hT_zero_of_mem_Xplus F (fun a => ?_) ?_
      · have := h (ℓ a.castSucc) (Submodule.subset_span ⟨_, rfl⟩)
        simpa [ℓ, Formalism.MainNotions.S.FlagG.fvec] using this
      · have := h (ℓ (Fin.last r)) (Submodule.subset_span ⟨_, rfl⟩)
        simpa [ℓ, Formalism.MainNotions.S.FlagG.fvec] using this
    · intro h φ hφ
      refine Submodule.span_induction (p := fun φ _ => φ v = 0) ?_ ?_ ?_ ?_ hφ
      · rintro _ ⟨a, rfl⟩
        exact h _ (fvec_mem_Xplus F a)
      · simp
      · intro x y _ _ hx hy
        simp [hx, hy]
      · intro c x _ hx
        simp [hx]
  have := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span E (Set.range ℓ))
  rw [hΦ, hco] at this
  omega

/- English proof (translation)
Introduce `x hx`. Rewrite using `[mem_orth_iff]`. Use `hT_zero_of_mem_Xplus F (fun a => ?_) ?_` and prove the remaining obligations. Conclude with `hT_swap_zero (hT_zero_of_mem_X F (fun b => F.e_iso b a) x hx)`. Conclude with `hT_swap_zero (hT_zero_of_mem_X F F.z_orth x hx)`.
-/
theorem X_le_orth_Xplus (F : Formalism.MainNotions.S.FlagG S r T) : F.X ≤ orth S F.Xplus := by
  intro x hx
  rw [mem_orth_iff]
  refine hT_zero_of_mem_Xplus F (fun a => ?_) ?_
  · exact hT_swap_zero (hT_zero_of_mem_X F (fun b => F.e_iso b a) x hx)
  · exact hT_swap_zero (hT_zero_of_mem_X F F.z_orth x hx)

/- English proof (translation)
Unfold `Formalism.MainNotions.S.FlagG.X`. Rewrite using `[finrank_span_eq_card F.e_indep]`. Simplify using the standard rewrite rules.
-/
theorem finrank_X (F : Formalism.MainNotions.S.FlagG S r T) : finrank E F.X = r := by
  unfold Formalism.MainNotions.S.FlagG.X
  rw [finrank_span_eq_card F.e_indep]; simp

end LinAlg

/- English proof (translation)
Rewrite using `[(D.sp.Y 0).rank_eq, D.sp.Y_rank 0 (Nat.zero_le _), Formalism.MainNotions.S.dimS_eq]`. Simplify using `[Ranks.rankY]`.
-/
theorem finrank_hS (D : D7) : finrank D.host.E (hS D).V = 2 * D.R.rS + D.R.k + 1 := by
  rw [(D.sp.Y 0).rank_eq, D.sp.Y_rank 0 (Nat.zero_le _), Formalism.MainNotions.S.dimS_eq]
  simp [Ranks.rankY]

/- English proof (translation)
Establish `hm : 0 < D.R.m` using `lt_of_lt_of_le (by norm_num) D.R.two_le_m`. Establish `hiso` using `D.sp.iXY_isom 0 hm`. Establish `hinj : Function.Injective (D.sp.iXY 0)`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `x hx`.

Rewrite `hx` using `[LinearMap.mem_ker]`. Use `(Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 x (fun y => ?_))` and prove the remaining obligations. Rewrite using `[← hiso y x, hx, map_zero]`. Establish `hle : Wsp D ≤ orth (hS D) (Xplus F)`. Introduce and unpack `_ ⟨x, rfl⟩`.

Rewrite using `[mem_orth_iff]`. Use `hT_zero_of_mem_Xplus F.fl (fun a => ?_) ?_` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `hT_swap_zero (D.sp.hyp_orthX a x).1`. Rewrite using `[hz]`.

Unfold `D7.zmOf`. Rewrite using `[map_smulₛₗ, LinearMap.smul_apply, hT_swap_zero (D.sp.zm_orth x), smul_zero]`. Establish `hbot : Wsp D ⊓ Xsp F = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce and unpack `_ ⟨⟨x, rfl⟩, hx⟩`.

Establish `h0 : x = 0`. Use `(D.sp.X 0).nondeg.2 x (fun y => ?_)` and prove the remaining obligations. Rewrite using `[← hiso y x]`. Use `hT_swap_zero (hT_zero_of_mem_X F.fl (fun a => ?_) _ hx)` and prove the remaining obligations. Rewrite using `[he]`.

Conclude with `hT_swap_zero (D.sp.hyp_orthX a y).1`. Rewrite using `[h0, map_zero]`. Conclude with `Submodule.zero_mem _`. Establish `hrk : finrank D.host.E (Wsp D) = D.R.k`. Unfold `Wsp`.

Rewrite using `[LinearMap.finrank_range_of_inj hinj, (D.sp.X 0).rank_eq, D.sp.X_rank 0 (Nat.zero_le _)]`. Simplify using `[Ranks.N]`. Use `⟨?_, hbot, hrk⟩` and prove the remaining obligations. Use `Submodule.eq_of_le_of_finrank_eq (sup_le hle (X_le_orth_Xplus F.fl)) ?_` and prove the remaining obligations. Establish `h3` using `Submodule.finrank_sup_add_finrank_inf_eq (Wsp D) (Xsp F)`.

Rewrite `h3` using `[hbot, finrank_bot]`. Establish `h4 : finrank D.host.E (orth (hS D) (Xplus F)) + (D.R.rS + 1) = finrank D.host.E (hS D).V` using `finrank_orth_Xplus F.fl (Nat.cast_ne_zero.2 hT : (T : D.host.E) ≠ 0)`. Establish `h5 : finrank D.host.E (Xsp F) = D.R.rS` using `finrank_X F.fl`. Establish `h6` using `finrank_hS D`. Use linear arithmetic over natural numbers and integers.
-/
theorem WHyp_Wsp (D : D7) (u : D.what₂.Word) {T : ℕ} (hT : T ≠ 0)
    (F : LFlag (hS D) D.R.rS (T : D.host.E)) (he : F.fl.e = D.sp.hypE) (hz : F.fl.z = D.zmOf u) :
    WHyp D F (Wsp D) := by
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  have hiso := D.sp.iXY_isom 0 hm
  have hinj : Function.Injective (D.sp.iXY 0) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    refine (Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 x (fun y => ?_))
    rw [← hiso y x, hx, map_zero]
  have hle : Wsp D ≤ orth (hS D) (Xplus F) := by
    rintro _ ⟨x, rfl⟩
    rw [mem_orth_iff]
    refine hT_zero_of_mem_Xplus F.fl (fun a => ?_) ?_
    · rw [he]; exact hT_swap_zero (D.sp.hyp_orthX a x).1
    · rw [hz]; unfold D7.zmOf
      rw [map_smulₛₗ, LinearMap.smul_apply, hT_swap_zero (D.sp.zm_orth x), smul_zero]
  have hbot : Wsp D ⊓ Xsp F = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨x, rfl⟩, hx⟩
    have h0 : x = 0 := by
      refine (D.sp.X 0).nondeg.2 x (fun y => ?_)
      rw [← hiso y x]
      refine hT_swap_zero (hT_zero_of_mem_X F.fl (fun a => ?_) _ hx)
      rw [he]; exact hT_swap_zero (D.sp.hyp_orthX a y).1
    rw [h0, map_zero]; exact Submodule.zero_mem _
  have hrk : finrank D.host.E (Wsp D) = D.R.k := by
    unfold Wsp
    rw [LinearMap.finrank_range_of_inj hinj, (D.sp.X 0).rank_eq, D.sp.X_rank 0 (Nat.zero_le _)]
    simp [Ranks.N]
  refine ⟨?_, hbot, hrk⟩
  refine Submodule.eq_of_le_of_finrank_eq (sup_le hle (X_le_orth_Xplus F.fl)) ?_
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (Wsp D) (Xsp F)
  rw [hbot, finrank_bot] at h3
  have h4 : finrank D.host.E (orth (hS D) (Xplus F)) + (D.R.rS + 1) = finrank D.host.E (hS D).V :=
    finrank_orth_Xplus F.fl (Nat.cast_ne_zero.2 hT : (T : D.host.E) ≠ 0)
  have h5 : finrank D.host.E (Xsp F) = D.R.rS := finrank_X F.fl
  have h6 := finrank_hS D
  omega

/- English proof (translation)
Take `⟨n, hn, hz⟩` from `hζ`. Take `⟨β, hβ⟩` from `hβ`. Assume the negation of the conclusion as `hne`. Establish `hβ0 : β ≠ 0`. Introduce and unpack `rfl`.

Apply `hne` to reduce the goal to its premises. Simplify `hβ` using `[sub_eq_zero]`. Establish `key : ∀ w : InfinitePlace K, w (β : K) < 1`. Introduce `w`. Establish `h1 : w (ζ : K) = 1`.

Establish `h : (w (ζ : K)) ^ n = 1`. Rewrite using `[← map_pow]`. Establish `: ((ζ : K)) ^ n = 1` using `by exact_mod_cast congrArg (fun x : 𝓞 K => (x : K)) hz`. Rewrite using `[this, map_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (apply_nonneg w _) hn.ne').1 h`.

Establish `h2 : w ((ζ : K) - 1) ≤ 2`. Establish `h21 : ‖w.embedding ((ζ : K) - 1)‖ ≤ ‖w.embedding (ζ : K)‖ + ‖w.embedding (1 : K)‖`. Rewrite using `[map_sub]`. Conclude with `norm_sub_le _ _`. Rewrite `h21` using `[InfinitePlace.norm_embedding_eq, InfinitePlace.norm_embedding_eq, InfinitePlace.norm_embedding_eq, h1, map_one]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : (ζ : K) - 1 = (T : K) * (β : K)`. Conclude with `congrArg (fun x : 𝓞 K => (x : K)) hβ` after adjusting the coercions. Establish `h4 : w (T : K) = T`. Rewrite using `[← InfinitePlace.norm_embedding_eq, map_natCast, Complex.norm_natCast]`.

Rewrite `h2` using `[h3, map_mul, h4]`. Establish `hT' : (3 : ℝ) ≤ T` using `by exact_mod_cast hT`. Establish `h5 : 0 ≤ w (β : K)` using `apply_nonneg w _`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨w⟩ : Nonempty (InfinitePlace K)` from `inferInstance`.

Establish `h` using `InfinitePlace.one_le_of_lt_one (w := w) hβ0 (fun z _ => key z)`. Conclude with `absurd (key w) (not_lt.mpr h)`.
-/
theorem rootOfUnity_eq_one_of_modT {K : Type} [Field K] [NumberField K] (T : ℕ) (hT : 3 ≤ T) (ζ : 𝓞 K)
    (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) (hβ : ∃ β : 𝓞 K, ζ - 1 = (T : 𝓞 K) * β) : ζ = 1 := by
  obtain ⟨n, hn, hz⟩ := hζ
  obtain ⟨β, hβ⟩ := hβ
  by_contra hne
  have hβ0 : β ≠ 0 := by
    rintro rfl
    apply hne
    simpa [sub_eq_zero] using hβ
  have key : ∀ w : InfinitePlace K, w (β : K) < 1 := by
    intro w
    have h1 : w (ζ : K) = 1 := by
      have h : (w (ζ : K)) ^ n = 1 := by
        rw [← map_pow]
        have : ((ζ : K)) ^ n = 1 := by exact_mod_cast congrArg (fun x : 𝓞 K => (x : K)) hz
        rw [this, map_one]
      exact (pow_eq_one_iff_of_nonneg (apply_nonneg w _) hn.ne').1 h
    have h2 : w ((ζ : K) - 1) ≤ 2 := by
      have h21 : ‖w.embedding ((ζ : K) - 1)‖ ≤ ‖w.embedding (ζ : K)‖ + ‖w.embedding (1 : K)‖ := by
        rw [map_sub]; exact norm_sub_le _ _
      rw [InfinitePlace.norm_embedding_eq, InfinitePlace.norm_embedding_eq,
        InfinitePlace.norm_embedding_eq, h1, map_one] at h21
      linarith
    have h3 : (ζ : K) - 1 = (T : K) * (β : K) := by
      exact_mod_cast congrArg (fun x : 𝓞 K => (x : K)) hβ
    have h4 : w (T : K) = T := by
      rw [← InfinitePlace.norm_embedding_eq, map_natCast, Complex.norm_natCast]
    rw [h3, map_mul, h4] at h2
    have hT' : (3 : ℝ) ≤ T := by exact_mod_cast hT
    have h5 : 0 ≤ w (β : K) := apply_nonneg w _
    nlinarith
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  have h := InfinitePlace.one_le_of_lt_one (w := w) hβ0 (fun z _ => key z)
  exact absurd (key w) (not_lt.mpr h)

/- English proof (translation)
Take `⟨_, hT, hT', h3, h3', hs, hs', _, _, _, hg, hc, hm⟩` from `h`. Conclude with `⟨hT, h3, hT', h3', hs, hs', hg, hc, hm, fun ζ hζ hβ => rootOfUnity_eq_one_of_modT _ h3 ζ hζ hβ⟩`.
-/
theorem VanishingOnXAndXPlus.primeHyp_of_stand (D : D7) (u u' : D.what₂.Word) (h : VanishingOnXAndXPlus.Stand D u u') :
    PrimeHyp D u (Tu D u') := by
  obtain ⟨_, hT, hT', h3, h3', hs, hs', _, _, _, hg, hc, hm⟩ := h
  exact ⟨hT, h3, hT', h3', hs, hs', hg, hc, hm,
    fun ζ hζ hβ => rootOfUnity_eq_one_of_modT _ h3 ζ hζ hβ⟩

/- English proof (translation)
The claim follows from `h u _`.
-/
theorem VanishingOnXAndXPlus.killer_conditions_of_stable (D : D7) (u u' : D.what₂.Word) (h : VanishingOnXAndXPlusGlobal.Conclusion1 D) : VanishingOnXAndXPlus.adm11 D u u' := h u _

/- English proof (translation)
The claim follows from `h u _`.
-/
theorem VanishingOnXAndXPlus.stable_lattice_of_no_served_orbit (D : D7) (u u' : D.what₂.Word) (h : VanishingOnXAndXPlusGlobal.Conclusion2 D) : VanishingOnXAndXPlus.adm12 D u u' := h u _

/- English proof (translation)
The claim follows from `h u _`.
-/
theorem VanishingOnXAndXPlus.level_clause_of_open_tool' (D : D7) (u u' : D.what₂.Word) (h : VanishingOnXAndXPlusGlobal.PointsLemma D) : VanishingOnXAndXPlus.adm13 D u u' := h u _

/- English proof (translation)
The claim follows from `h u _`.
-/
theorem VanishingOnXAndXPlus.module_clause_of_tools (D : D7) (u u' : D.what₂.Word) (h : VanishingOnXAndXPlusGlobal.Conclusion4 D) : VanishingOnXAndXPlus.adm14 D u u' := h u _

/- English proof (translation)
The claim follows from `h u _`.
-/
theorem VanishingOnXAndXPlus.truncation_clause_of_tools (D : D7) (u u' : D.what₂.Word) (h : VanishingOnXAndXPlusGlobal.PairsWithFiniteGroup D) : VanishingOnXAndXPlus.adm15 D u u' := h u _

section Cnt
variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ)

/- English proof (translation)
Introduce `hH` and use `(h hH).1`.
-/
theorem AuxiliaryNormPrimes.mass_third_of_source (C c : ℝ) (h : VanishingOnXAndXPlusMass.Conclusion1 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C c) :
    AuxiliaryNormPrimes.RankTwoMassBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := fun hH => (h hH).1
/- English proof (translation)
Introduce `hH` and use `(h hH).1`.
-/
theorem VanishingOnXAndXPlus.integrality_clause_of_full (C c : ℝ) (h : VanishingOnXAndXPlusMass.Conclusion1 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C c) :
    VanishingOnXAndXPlus.IntegralityRemainder D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := fun hH => (h hH).1

end Cnt

section Amp
variable (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 A : ℝ)

/- English proof (translation)
The claim follows from `h`.
-/
theorem VanishingOnXAndXPlus.energy_third_bound_of_reduction (C1 C : ℝ) (h : VanishingOnXAndXPlusBranching.Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 C1 C) : VanishingOnXAndXPlus.adm22 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C :=
  h

/- English proof (translation)
Assemble the required witnesses or components as `⟨VanishingOnXAndXPlus.energy_third_bound_of_reduction D large₂ _ _ _ _ _ _ _ _ _ C1 C h.1, h.2⟩`.
-/
theorem VanishingOnXAndXPlus.eight_amplitude_bounds_of_source (C1 Cpr C C2 Ch δ : ℝ) (h : VanishingOnXAndXPlusBranching.aux₃ D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ) :
    VanishingOnXAndXPlus.AmplitudeBoundsConjunction D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ :=
  ⟨VanishingOnXAndXPlus.energy_third_bound_of_reduction D large₂ _ _ _ _ _ _ _ _ _ C1 C h.1, h.2⟩

end Amp

/- English proof (translation)
The claim follows from `|Q - P| ≤ (a - 1) * P := by have key : (a + 1) * ((b + a - 2) * P) = (a - 1) * (a * P - b * P) := by linear_combination (2 * P) * hab have h3 : 0 ≤ (a + 1) * ((b + a - 2) * P) := by rw [key]; exact mul_nonneg (by linarith) (by linarith) have h4 : 0 ≤ (b + a - 2) * P := (mul_nonne …`.
-/
theorem abs_sub_le_of_two_sided {a b P Q : ℝ} (ha : 1 ≤ a) (hab : a * b = 1) (h1 : b * P ≤ Q) (h2 : Q ≤ a * P) :
    |Q - P| ≤ (a - 1) * P := by
  have key : (a + 1) * ((b + a - 2) * P) = (a - 1) * (a * P - b * P) := by linear_combination (2 * P) * hab
  have h3 : 0 ≤ (a + 1) * ((b + a - 2) * P) := by
    rw [key]; exact mul_nonneg (by linarith) (by linarith)
  have h4 : 0 ≤ (b + a - 2) * P := (mul_nonneg_iff_of_pos_left (by linarith)).1 h3
  rw [abs_le]
  constructor <;> nlinarith

def epsT (D : D7) : ℝ := Real.exp ((D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k)) - 1

/- English proof (translation)
The claim follows from `|D.what₂.Dstar / (D.duS w : ℝ) - ∏ τ, (Formalism.MainNotions.S.Tcrit D w τ / Formalism.MainNotions.S.Tr D w) ^ D.R.k| ≤ epsT D * ∏ τ, (Formalism.MainNotions.S.Tcrit D w τ / Formalism.MainNotions.S.Tr D w) ^ D.R.k := by obtain ⟨h1, h2⟩ := h w refine abs_sub_le_of_two_sided (Real.o …`.
-/
theorem tprod_of_27 (D : D7) (h : LocalBesselAndTopKernel.projection_sandwich_lattice D) (w : D.what₂.Word) :
    |D.what₂.Dstar / (D.duS w : ℝ) - ∏ τ, (Formalism.MainNotions.S.Tcrit D w τ / Formalism.MainNotions.S.Tr D w) ^ D.R.k| ≤
      epsT D * ∏ τ, (Formalism.MainNotions.S.Tcrit D w τ / Formalism.MainNotions.S.Tr D w) ^ D.R.k := by
  obtain ⟨h1, h2⟩ := h w
  refine abs_sub_le_of_two_sided (Real.one_le_exp (by positivity)) ?_ h1 h2
  rw [← Real.exp_add]; simp

section Tprod
variable (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)

/- English proof (translation)
Introduce `hH w` and use `tprod_of_27 D (h ⟨hH.2.1, hH.1, hH.2.2⟩) w`.
-/
theorem VanishingOnXAndXPlusMass.lemma_M_prime_hypothesis (h : LocalBesselAndTopKernel.hyp D large₂ C0 C' Cl Cg cb Cu cT CT → LocalBesselAndTopKernel.projection_sandwich_lattice D) :
    VanishingOnXAndXPlusMass.adm8 D large₂ C' Cl Cg cb Cu cT CT C0 (epsT D) := fun hH w => tprod_of_27 D (h ⟨hH.2.1, hH.1, hH.2.2⟩) w

end Tprod

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

/- English proof (translation)
Introduce `x i u u'` and use `VanishingOnXAndXPlus.killer_conditions_of_stable _ u u' (h x i)`.
-/
theorem VanishingOnXAndXPlus.family_hermitian_words_of_source (h : VanishingOnXAndXPlusGlobal.ConclusionF1 Fm) : VanishingOnXAndXPlus.FamilyWeylAndVandermonde Fm := fun x i u u' => VanishingOnXAndXPlus.killer_conditions_of_stable _ u u' (h x i)
/- English proof (translation)
Introduce `x i u u'` and use `VanishingOnXAndXPlus.stable_lattice_of_no_served_orbit _ u u' (h x i)`.
-/
theorem VanishingOnXAndXPlus.family_gluing_twelve_of_setting (h : VanishingOnXAndXPlusGlobal.ConclusionF2 Fm) : VanishingOnXAndXPlus.FamilyTwelfthHypothesis Fm := fun x i u u' => VanishingOnXAndXPlus.stable_lattice_of_no_served_orbit _ u u' (h x i)
/- English proof (translation)
Introduce `x i u u'` and use `VanishingOnXAndXPlus.level_clause_of_open_tool' _ u u' (h x i)`.
-/
theorem VanishingOnXAndXPlus.family_size_bounds_of_source (h : VanishingOnXAndXPlusGlobal.ConclusionF3 Fm) : VanishingOnXAndXPlus.FamilyThirteenthHypothesis Fm := fun x i u u' => VanishingOnXAndXPlus.level_clause_of_open_tool' _ u u' (h x i)
/- English proof (translation)
Introduce `x i u u'` and use `VanishingOnXAndXPlus.module_clause_of_tools _ u u' (h x i)`.
-/
theorem VanishingOnXAndXPlus.family_gluing_fourteen_of_setting (h : VanishingOnXAndXPlusGlobal.FamilyEstimateFour Fm) : VanishingOnXAndXPlus.FamilyFourteenthHypothesis Fm := fun x i u u' => VanishingOnXAndXPlus.module_clause_of_tools _ u u' (h x i)
/- English proof (translation)
Introduce `x i u u'` and use `VanishingOnXAndXPlus.truncation_clause_of_tools _ u u' (h x i).2`.
-/
theorem VanishingOnXAndXPlus.family_lemma_E_prime_of_source (h : VanishingOnXAndXPlusGlobal.ConclusionF5 Fm) : VanishingOnXAndXPlus.FamilyFifteenthHypothesis Fm := fun x i u u' => VanishingOnXAndXPlus.truncation_clause_of_tools _ u u' (h x i).2

variable (Cg cb Cu cT CT C0 A : ℝ)

/- English proof (translation)
Take `⟨C, c, hC⟩` from `h`. Conclude with `⟨C, Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i H u u' => AuxiliaryNormPrimes.mass_third_of_source _ _ u u' _ _ _ _ _ _ _ _ _ C c (H u u')) hC⟩`.
-/
theorem AuxiliaryNormPrimes.family_mass_third_of_source (h : VanishingOnXAndXPlusMass.Conclusion1Family Fm Cg cb Cu cT CT C0 A) : AuxiliaryNormPrimes.FamilyRankTwoMassBound Fm Cg cb Cu cT CT C0 A := by
  obtain ⟨C, c, hC⟩ := h
  exact ⟨C, Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i H u u' => AuxiliaryNormPrimes.mass_third_of_source _ _ u u' _ _ _ _ _ _ _ _ _ C c (H u u')) hC⟩
/- English proof (translation)
Take `⟨C, c, hC⟩` from `h`. Conclude with `⟨C, Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i H u u' => VanishingOnXAndXPlus.integrality_clause_of_full _ _ u u' _ _ _ _ _ _ _ _ _ C c (H u u')) hC⟩`.
-/
theorem VanishingOnXAndXPlus.family_mass_of_source (h : VanishingOnXAndXPlusMass.Conclusion1Family Fm Cg cb Cu cT CT C0 A) : VanishingOnXAndXPlus.FamilyRankTwoMassEstimate Fm Cg cb Cu cT CT C0 A := by
  obtain ⟨C, c, hC⟩ := h
  exact ⟨C, Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i H u u' => VanishingOnXAndXPlus.integrality_clause_of_full _ _ u u' _ _ _ _ _ _ _ _ _ C c (H u u')) hC⟩
/- English proof (translation)
The claim follows from `h`.
-/
theorem VanishingOnXAndXPlus.family_second_sum_of_source (h : VanishingOnXAndXPlusMass.Conclusion3Family Fm) : VanishingOnXAndXPlus.FamilyTotalRowMassIdentity Fm := h

/- English proof (translation)
Take `⟨C, C2, Ch, hC⟩` from `h`. Conclude with `⟨C, C2, Ch, fun Cpr δ hδ => Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i H => VanishingOnXAndXPlus.eight_amplitude_bounds_of_source _ _ _ _ _ _ _ _ _ _ _ C1 Cpr C C2 Ch δ H) (hC Cpr δ hδ)⟩`.
-/
theorem VanishingOnXAndXPlus.family_amplitude_of_source (C1 : ℝ) (h : VanishingOnXAndXPlusBranching.FamilyTargetsAtConstants Fm Cg cb Cu cT CT C0 A C1) : VanishingOnXAndXPlus.FamilyAmplitudeBoundsShared Fm Cg cb Cu cT CT C0 A C1 := by
  obtain ⟨C, C2, Ch, hC⟩ := h
  exact ⟨C, C2, Ch, fun Cpr δ hδ => Formalism.MainNotions.S.OwnEv.mono
    (fun C' Cl x i H => VanishingOnXAndXPlus.eight_amplitude_bounds_of_source _ _ _ _ _ _ _ _ _ _ _ C1 Cpr C C2 Ch δ H) (hC Cpr δ hδ)⟩

end Fam

/- English proof (translation)
Introduce `Λ hL hU U hN` and use `⟨(h Λ hL hU U hN).2.2.1, (h Λ hL hU U hN).2.2.2⟩`.
-/
theorem VanishingOnXAndXPlusGluing.gluing_contains_setting (D : D7) (h : VanishingOnXAndXPlusGlobal.adm1 D) : VanishingOnXAndXPlusGluing.adm1 D :=
  fun Λ hL hU U hN => ⟨(h Λ hL hU U hN).2.2.1, (h Λ hL hU U hN).2.2.2⟩

section Same
variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ)

end Same

section Bridge

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Bridge
open scoped ENNReal

def TFrameOfHyp (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ w, 1 ≤ Tr D w * kaS D ^ (2 * D.R.rS)

/- English proof (translation)
Unfold `hsNormSq hsInner`. Rewrite using `[Complex.re_sum]`. Conclude with `Finset.sum_nonneg (fun i _ => by simpa using inner_self_nonneg (𝕜 := ℂ) (x := A (stdOrthonormalBasis ℂ Wq i)))`.
-/
theorem hsNormSq_nonneg {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  exact Finset.sum_nonneg (fun i _ => by simpa using inner_self_nonneg (𝕜 := ℂ) (x := A (stdOrthonormalBasis ℂ Wq i)))

/- English proof (translation)
Establish `hL : 1 ≤ large₂.sc.L` using `Real.one_le_rpow (le_of_lt large₂.sc.one_lt_alt) (le_of_lt large₂.sc.eps_pos)`. Unfold `Scale.b`. Rewrite using `[← Real.exp_mul]`. Conclude with `Real.exp_le_exp.2 (by nlinarith)`.
-/
theorem exp_one_le_b_rpow {D : D7} (large₂ : SizeData₂ D) {Cβ : ℝ} (hβ : 1 ≤ Cβ) : Real.exp 1 ≤ large₂.sc.b ^ Cβ := by
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow (le_of_lt large₂.sc.one_lt_alt) (le_of_lt large₂.sc.eps_pos)
  unfold Scale.b
  rw [← Real.exp_mul]
  exact Real.exp_le_exp.2 (by nlinarith)

/- English proof (translation)
Introduce `hH τ w w' hTT θ hθ W hW lam' hl A hA μsec hμ γ p hRel θ' hθ' νR hνR`. Establish `hT : 0 < Tr D w` using `Nat.cast_pos.2 hTT.1.pos`. Establish `hT' : 0 < Tr D w'` using `Nat.cast_pos.2 hTT.2.1.pos`. Establish `hm : ((2 * D.R.rS + 2 : ℕ) : ℝ) = (D.R.m : ℝ)`. Establish `h1` using `dimS_eq D.R`.

Establish `h2` using `D.R.two_le_m`. Unfold `Ranks.r at h1`. Establish `h3 : 2 * D.R.rS + 2 = D.R.m` using `by omega`. Conclude with `h3` after adjusting the coercions. Establish `hb0 : 0 < large₂.sc.b` using `Real.exp_pos _`.

Establish `hbβ : 0 < large₂.sc.b ^ Cβ` using `Real.rpow_pos_of_pos hb0 _`. Take `⟨f, K, hK, hf, hN, hJ⟩` from `hAmp hH τ w w' hTT θ hθ W hW lam' hl A hA hT hT'`. Take `⟨hN0, hMM⟩` from `hN μsec hμ`. Establish `hJ'` using `hJ γ p hRel θ' hθ' νR hνR`. Take `⟨hStd1, hGaps⟩` from `hStd hH τ w w'`.

Establish `hka : 0 < kaS D` using `hStd1.2.2.2.1`. Establish `hTzW : Tz D.R.k D.R.rS W.z = Tr D w` using `hW.2.2.2.2.1`. Establish `hTzW' : Tz D.R.k D.R.rS W.z' = Tr D w'` using `hW.2.2.2.2.2.1`. Establish `hv5 : 0 < D.host.v` using `by unfold Formalism.BasicNotions.Host.v; linarith [rdE_pos D]`. Establish `hθ5 : 0 < θ` using `lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ.1`.

Establish `hκ5 : 0 < kapN D θ`. Unfold `kapN`. Conclude with `ENNReal.ofReal_pos.2 (mul_pos (Real.rpow_pos_of_pos (by positivity) _) hθ5)`. Take `⟨L₁, f₁, hε, hlam, hu, hu', hc, hκ0, hκT, hTz, hTz', hf₁, hrest⟩` from `hFr (toBessel D τ w w' θ W lam' A hW hA hT hT') (lamD D τ) f (kaS D) (large₂.sc.b ^ Cβ) (exp_one_le_b_rpow large₂ hβ) hka hStd1.2.2.2.2.1 hStd1.2.2.2.2.2.1 (by show ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) = ((2 * kaS D : ℝ) : ℂ)`. Use `congr 1`.

Unfold `kaS gg`. Use the proof step `ring)`. Use the proof step `ENNReal.ofReal_ne_top rfl hκ5`. Use the proof step `(by show StdHyp Ch Cs D.R.k D.R.rS (epsSH D.R) (lamD D τ) (uS D w τ) (uS D w' τ) (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') (kaS D) (large₂.sc.b ^ Cβ)`. Rewrite using `[hTzW, hTzW']`.

Conclude with `hStd1)`. Use `hl hf`. Take `⟨μsec₁, hμ₁, K₁, hK₁, hN1, hN1ne, hpts⟩` from `hrest μsec hμ`. Establish `hGeq : Gf D.R.k D.R.rS W.z W.z' γ = Gpt (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p` using `hG W.z W.z' γ p hRel`. Establish `hGp : Gpt (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p ≠ 0` using `by rw [← hGeq]; exact hRel.2.2`.

Take `⟨p₁, hG1, hGmax, hO⟩` from `hpts p hGp`. Establish `h1k : 1 ≤ D.R.k`. Establish `h1 : D.R.m ^ 4 ≤ D.R.f` using `hH.1.2.2.1`. Establish `h2 : D.R.f ≤ D.R.k` using `hH.1.2.2.2.1`. Establish `h3 : 1 ≤ D.R.m ^ 4` using `Nat.one_le_pow _ _ (lt_of_lt_of_le (by norm_num) D.R.two_le_m)`.

Use linear arithmetic over natural numbers and integers. Establish `e1 : Tz D.R.k D.R.rS L₁.z * (1 / kaS D) ^ (2 * D.R.rS) = Tr D w`. Rewrite using `[hTz, mul_assoc, ← mul_pow, mul_one_div_cancel hka.ne', one_pow, mul_one]`. Conclude with `hTzW`. Establish `e2 : Tz D.R.k D.R.rS L₁.z' * (1 / kaS D) ^ (2 * D.R.rS) = Tr D w'`.

Rewrite using `[hTz', mul_assoc, ← mul_pow, mul_one_div_cancel hka.ne', one_pow, mul_one]`. Conclude with `hTzW'`. Establish `hLoc : LocOk D Ch Cs L₁ (lamD D τ) (kaS D) (large₂.sc.b ^ Cβ) 1`. Use `⟨h1k, hε, hc, hκ0, hκT, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hε, hu, hu', e1, e2]`.

Conclude with `hStd1`. Rewrite using `[one_pow, mul_one, hTz]`. Conclude with `hTzW ▸ hTF hH w`. Rewrite using `[one_pow, mul_one, hTz']`. Conclude with `hTzW' ▸ hTF hH w'`.

Establish `hRng : OnePlaceEstimates.RngU D Cn Cs' L₁.lam (lamD D τ)`. Use `⟨hGaps, ?_⟩` and prove the remaining obligations. Rewrite using `[hlam, hm]`. Conclude with `hl`. Establish `hB` using `h47 L₁ (lamD D τ) f₁ μsec₁ (kaS D) (large₂.sc.b ^ Cβ) hLoc hRng hf₁ hμ₁ (hN1ne hN0) p₁ hG1`.

Unfold `BpIneq at hB`. Rewrite `hB` using `[hm]`. Rewrite using `[← hTzW, ← hTzW']`. Distinguish the cases in `hw0 : ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p ≤ 0`. Rewrite using `[ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hw0 (hsNormSq_nonneg _))]`.

Conclude with `zero_le`. Establish `hw0' : 0 < ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p` using `not_le.1 hw0`. Establish `hXf : 0 < (large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2)` using `Real.rpow_pos_of_pos hbβ _`. Establish `hXa : 0 < large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)` using `Real.rpow_pos_of_pos hb0 _`. Establish `hreal : large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2) * ((large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2) * ((large₂.sc.b ^ Cβ) ^ (Cb * (D.R.m : ℝ) ^ 4) * (max 1 (1 / Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁)) ^ (Cb * (D.R.m : ℝ) ^ 2))) ≤ large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 4) * (max …`.

Rewrite using `[hGeq, ← one_div]`. Use `le_trans ?_ (hC _ (le_max_left _ _))` and prove the remaining obligations. Establish `h5 : (max 1 (1 / Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁)) ^ (Cb * (D.R.m : ℝ) ^ 2) ≤ ((large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2) * max 1 (1 / Gpt (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p)) ^ (Cb * (D.R.m : ℝ) ^ 2)` using `Real.rpow_le_rpow (le_trans zero_le_one (le_max_left _ _)) hGmax (by positivity)`. Establish `h6 : 0 < (large₂.sc.b ^ Cβ) ^ (Cb * (D.R.m : ℝ) ^ 4)` using `Real.rpow_pos_of_pos hbβ _`. Use `gcongr`.

Establish `step : ENNReal.ofReal K₁ * ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p * hsNormSq (A.J νR γ)) ≤ ENNReal.ofReal K₁ * (ENNReal.ofReal (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 4) * (max 1 (Gf D.R.k D.R.rS W.z W.z' γ)⁻¹) ^ (C * (D.R.m : ℝ) ^ 2)) * MM …`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.ofReal_mul hK₁.le, ← mul_assoc, ENNReal.ofReal_mul (by positivity)]`. Use `_ ≤ ENNReal.ofReal (K₁ * ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p) * (ENNReal.ofReal (K * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) * orbSqO (toBessel D τ w w' θ W lam' A hW hA hT hT') f p) := by gcongr`. Use `_ = ENNReal.ofReal (K * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) * (ENNReal.ofReal (K₁ * ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p) * orbSqO (toBessel D τ w w' θ W lam' A hW hA hT hT') f p) := by ring`.

Use `_ ≤ ENNReal.ofReal (K * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) * (ENNReal.ofReal ((large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2) * ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁) * orbSq L₁ f₁ p₁) := by`. Conclude with `mul_le_mul' le_rfl hO`. Use `_ = ENNReal.ofReal (K * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) * (ENNReal.ofReal ((large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2)) * (ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁) * orbSq L₁ f₁ p₁)) := by`. Rewrite using `[ENNReal.ofReal_mul hXf.le]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ ENNReal.ofReal (K * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) * (ENNReal.ofReal ((large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2)) * (ENNReal.ofReal ((large₂.sc.b ^ Cβ) ^ (Cb * (D.R.m : ℝ) ^ 4) * (max 1 (1 / Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁)) ^ (Cb * (D.R.m : ℝ) ^ …`. Conclude with `mul_le_mul' le_rfl (mul_le_mul' le_rfl (le_trans hB (mul_le_mul' le_rfl hN1)))`. Use `_ = ENNReal.ofReal K₁ * (ENNReal.ofReal (large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2) * ((large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2) * ((large₂.sc.b ^ Cβ) ^ (Cb * (D.R.m : ℝ) ^ 4) * (max 1 (1 / Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁)) ^ (Cb * (D.R.m : ℝ) ^ 2)))) * (ENNReal …`. Rewrite using `[ENNReal.ofReal_mul hK.le, ENNReal.ofReal_mul hXa.le, ENNReal.ofReal_mul hXf.le]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ _ := by gcongr`. Conclude with `(ENNReal.mul_le_mul_iff_right (by simpa using hK₁) ENNReal.ofReal_ne_top).1 step`.
-/
theorem AuxiliaryNormPrimes.partial_trace_of_frames (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 Ca Ch Cf Cs Cs' Cβ Cb C : ℝ)
    (hAmp : AmpIsBessel D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Ca) (hFr : FrameChange D Ch Cs Cn Cf)
    (hStd : StdOfHyp D large₂ C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ) (hTF : TFrameOfHyp D large₂ C' Cl Cg cb Cu cT CT C0) (hG : GfOfRelPt D)
    (h47 : OnePlaceEstimates.UniformityTheoremBPrime D Ch Cn Cs Cs' Cb) (hβ : 1 ≤ Cβ) (hCb : 0 ≤ Cb)
    (hC : ∀ x : ℝ, 1 ≤ x →
      large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2) * ((large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2) *
        ((large₂.sc.b ^ Cβ) ^ (Cb * (D.R.m : ℝ) ^ 4) *
          ((large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2) * x) ^ (Cb * (D.R.m : ℝ) ^ 2))) ≤
      large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 4) * x ^ (C * (D.R.m : ℝ) ^ 2)) :
    AuxiliaryNormPrimes.PlancherelBoundOneParameter D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro hH τ w w' hTT θ hθ W hW lam' hl A hA μsec hμ γ p hRel θ' hθ' νR hνR
  have hT : 0 < Tr D w := Nat.cast_pos.2 hTT.1.pos
  have hT' : 0 < Tr D w' := Nat.cast_pos.2 hTT.2.1.pos
  have hm : ((2 * D.R.rS + 2 : ℕ) : ℝ) = (D.R.m : ℝ) := by
    have h1 := dimS_eq D.R
    have h2 := D.R.two_le_m
    unfold Ranks.r at h1
    have h3 : 2 * D.R.rS + 2 = D.R.m := by omega
    exact_mod_cast h3
  have hb0 : 0 < large₂.sc.b := Real.exp_pos _
  have hbβ : 0 < large₂.sc.b ^ Cβ := Real.rpow_pos_of_pos hb0 _
  obtain ⟨f, K, hK, hf, hN, hJ⟩ := hAmp hH τ w w' hTT θ hθ W hW lam' hl A hA hT hT'
  obtain ⟨hN0, hMM⟩ := hN μsec hμ
  have hJ' := hJ γ p hRel θ' hθ' νR hνR
  obtain ⟨hStd1, hGaps⟩ := hStd hH τ w w'
  have hka : 0 < kaS D := hStd1.2.2.2.1
  have hTzW : Tz D.R.k D.R.rS W.z = Tr D w := hW.2.2.2.2.1
  have hTzW' : Tz D.R.k D.R.rS W.z' = Tr D w' := hW.2.2.2.2.2.1
  have hv5 : 0 < D.host.v := by unfold Formalism.BasicNotions.Host.v; linarith [rdE_pos D]
  have hθ5 : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ.1
  have hκ5 : 0 < kapN D θ := by
    unfold kapN
    exact ENNReal.ofReal_pos.2 (mul_pos (Real.rpow_pos_of_pos (by positivity) _) hθ5)
  obtain ⟨L₁, f₁, hε, hlam, hu, hu', hc, hκ0, hκT, hTz, hTz', hf₁, hrest⟩ :=
    hFr (toBessel D τ w w' θ W lam' A hW hA hT hT') (lamD D τ) f (kaS D) (large₂.sc.b ^ Cβ) (exp_one_le_b_rpow large₂ hβ) hka
      hStd1.2.2.2.2.1 hStd1.2.2.2.2.2.1
      (by
        show ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) = ((2 * kaS D : ℝ) : ℂ)
        congr 1
        unfold kaS gg
        ring)
      ENNReal.ofReal_ne_top rfl hκ5
      (by
        show StdHyp Ch Cs D.R.k D.R.rS (epsSH D.R) (lamD D τ) (uS D w τ) (uS D w' τ) (Tz D.R.k D.R.rS W.z)
          (Tz D.R.k D.R.rS W.z') (kaS D) (large₂.sc.b ^ Cβ)
        rw [hTzW, hTzW']
        exact hStd1)
      hl hf
  obtain ⟨μsec₁, hμ₁, K₁, hK₁, hN1, hN1ne, hpts⟩ := hrest μsec hμ
  have hGeq : Gf D.R.k D.R.rS W.z W.z' γ = Gpt (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p := hG W.z W.z' γ p hRel
  have hGp : Gpt (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p ≠ 0 := by rw [← hGeq]; exact hRel.2.2
  obtain ⟨p₁, hG1, hGmax, hO⟩ := hpts p hGp
  have h1k : 1 ≤ D.R.k := by
    have h1 : D.R.m ^ 4 ≤ D.R.f := hH.1.2.2.1
    have h2 : D.R.f ≤ D.R.k := hH.1.2.2.2.1
    have h3 : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (lt_of_lt_of_le (by norm_num) D.R.two_le_m)
    omega
  have e1 : Tz D.R.k D.R.rS L₁.z * (1 / kaS D) ^ (2 * D.R.rS) = Tr D w := by
    rw [hTz, mul_assoc, ← mul_pow, mul_one_div_cancel hka.ne', one_pow, mul_one]; exact hTzW
  have e2 : Tz D.R.k D.R.rS L₁.z' * (1 / kaS D) ^ (2 * D.R.rS) = Tr D w' := by
    rw [hTz', mul_assoc, ← mul_pow, mul_one_div_cancel hka.ne', one_pow, mul_one]; exact hTzW'
  have hLoc : LocOk D Ch Cs L₁ (lamD D τ) (kaS D) (large₂.sc.b ^ Cβ) 1 := by
    refine ⟨h1k, hε, hc, hκ0, hκT, ?_, ?_, ?_⟩
    · rw [hε, hu, hu', e1, e2]
      exact hStd1
    · rw [one_pow, mul_one, hTz]
      exact hTzW ▸ hTF hH w
    · rw [one_pow, mul_one, hTz']
      exact hTzW' ▸ hTF hH w'
  have hRng : OnePlaceEstimates.RngU D Cn Cs' L₁.lam (lamD D τ) := by
    refine ⟨hGaps, ?_⟩
    rw [hlam, hm]
    exact hl
  have hB := h47 L₁ (lamD D τ) f₁ μsec₁ (kaS D) (large₂.sc.b ^ Cβ) hLoc hRng hf₁ hμ₁ (hN1ne hN0) p₁ hG1
  unfold BpIneq at hB
  rw [hm] at hB
  rw [← hTzW, ← hTzW']
  by_cases hw0 : ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p ≤ 0
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hw0 (hsNormSq_nonneg _))]
    exact zero_le
  have hw0' : 0 < ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p := not_le.1 hw0
  have hXf : 0 < (large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2) := Real.rpow_pos_of_pos hbβ _
  have hXa : 0 < large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2) := Real.rpow_pos_of_pos hb0 _
  have hreal : large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2) * ((large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2) *
      ((large₂.sc.b ^ Cβ) ^ (Cb * (D.R.m : ℝ) ^ 4) *
        (max 1 (1 / Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁)) ^ (Cb * (D.R.m : ℝ) ^ 2))) ≤
      large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 4) *
        (max 1 (Gf D.R.k D.R.rS W.z W.z' γ)⁻¹) ^ (C * (D.R.m : ℝ) ^ 2) := by
    rw [hGeq, ← one_div]
    refine le_trans ?_ (hC _ (le_max_left _ _))
    have h5 : (max 1 (1 / Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁)) ^ (Cb * (D.R.m : ℝ) ^ 2) ≤
        ((large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2) *
          max 1 (1 / Gpt (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p)) ^ (Cb * (D.R.m : ℝ) ^ 2) :=
      Real.rpow_le_rpow (le_trans zero_le_one (le_max_left _ _)) hGmax (by positivity)
    have h6 : 0 < (large₂.sc.b ^ Cβ) ^ (Cb * (D.R.m : ℝ) ^ 4) := Real.rpow_pos_of_pos hbβ _
    gcongr
  have step : ENNReal.ofReal K₁ * ENNReal.ofReal
        (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p * hsNormSq (A.J νR γ)) ≤
      ENNReal.ofReal K₁ * (ENNReal.ofReal (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 4) *
        (max 1 (Gf D.R.k D.R.rS W.z W.z' γ)⁻¹) ^ (C * (D.R.m : ℝ) ^ 2)) * MMv D w w' A μsec) := by
    calc ENNReal.ofReal K₁ * ENNReal.ofReal
          (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p * hsNormSq (A.J νR γ))
        = ENNReal.ofReal (K₁ * ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p) *
            ENNReal.ofReal (hsNormSq (A.J νR γ)) := by
          rw [← ENNReal.ofReal_mul hK₁.le, ← mul_assoc, ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (K₁ * ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p) *
            (ENNReal.ofReal (K * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) *
              orbSqO (toBessel D τ w w' θ W lam' A hW hA hT hT') f p) := by gcongr
      _ = ENNReal.ofReal (K * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) *
            (ENNReal.ofReal (K₁ * ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') p) *
              orbSqO (toBessel D τ w w' θ W lam' A hW hA hT hT') f p) := by ring
      _ ≤ ENNReal.ofReal (K * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) *
            (ENNReal.ofReal ((large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2) *
              ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁) * orbSq L₁ f₁ p₁) := by
          exact mul_le_mul' le_rfl hO
      _ = ENNReal.ofReal (K * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) *
            (ENNReal.ofReal ((large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2)) *
              (ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁) *
                orbSq L₁ f₁ p₁)) := by
          rw [ENNReal.ofReal_mul hXf.le]; ring
      _ ≤ ENNReal.ofReal (K * large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2)) *
            (ENNReal.ofReal ((large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2)) *
              (ENNReal.ofReal ((large₂.sc.b ^ Cβ) ^ (Cb * (D.R.m : ℝ) ^ 4) *
                (max 1 (1 / Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁)) ^ (Cb * (D.R.m : ℝ) ^ 2)) *
                (ENNReal.ofReal K₁ * jNorm2 (toBessel D τ w w' θ W lam' A hW hA hT hT') f μsec))) := by
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (le_trans hB (mul_le_mul' le_rfl hN1)))
      _ = ENNReal.ofReal K₁ * (ENNReal.ofReal (large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2) *
            ((large₂.sc.b ^ Cβ) ^ (Cf * (D.R.m : ℝ) ^ 2) * ((large₂.sc.b ^ Cβ) ^ (Cb * (D.R.m : ℝ) ^ 4) *
              (max 1 (1 / Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') p₁)) ^ (Cb * (D.R.m : ℝ) ^ 2)))) *
            (ENNReal.ofReal K * jNorm2 (toBessel D τ w w' θ W lam' A hW hA hT hT') f μsec)) := by
          rw [ENNReal.ofReal_mul hK.le, ENNReal.ofReal_mul hXa.le, ENNReal.ofReal_mul hXf.le]; ring
      _ ≤ _ := by
          gcongr
  exact (ENNReal.mul_le_mul_iff_right (by simpa using hK₁) ENNReal.ofReal_ne_top).1 step

/- English proof (translation)
Establish `hb0 : 0 ≤ b` using `by linarith`. Establish `hbp : 0 < b` using `by linarith`. Establish `hx0 : 0 ≤ x` using `by linarith`. Establish `e1 : (b ^ Cβ) ^ (Cf * m ^ 2) = b ^ (Cβ * (Cf * m ^ 2))` using `(Real.rpow_mul hb0 _ _).symm`. Establish `e2 : (b ^ Cβ) ^ (Cb * m ^ 4) = b ^ (Cβ * (Cb * m ^ 4))` using `(Real.rpow_mul hb0 _ _).symm`.

Establish `e3 : (b ^ (Cβ * (Cf * m ^ 2)) * x) ^ (Cb * m ^ 2) = b ^ (Cβ * (Cf * m ^ 2) * (Cb * m ^ 2)) * x ^ (Cb * m ^ 2)`. Rewrite using `[Real.mul_rpow (Real.rpow_nonneg hb0 _) hx0, ← Real.rpow_mul hb0]`. Rewrite using `[e1, e2, e3]`. Establish `e4 : b ^ (Ca * m ^ 2) * (b ^ (Cβ * (Cf * m ^ 2)) * (b ^ (Cβ * (Cb * m ^ 4)) * (b ^ (Cβ * (Cf * m ^ 2) * (Cb * m ^ 2)) * x ^ (Cb * m ^ 2)))) = b ^ (Ca * m ^ 2 + Cβ * (Cf * m ^ 2) + Cβ * (Cb * m ^ 4) + Cβ * (Cf * m ^ 2) * (Cb * m ^ 2)) * x ^ (Cb * m ^ 2)`. Rewrite using `[Real.rpow_add hbp, Real.rpow_add hbp, Real.rpow_add hbp]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e4]`. Establish `hs1 : 1 ≤ m ^ 2` using `by nlinarith`. Establish `hs : m ^ 2 ≤ m ^ 4` using `by nlinarith`. Establish `h4 : 0 ≤ m ^ 4` using `by positivity`.

Establish `hexp : Ca * m ^ 2 + Cβ * (Cf * m ^ 2) + Cβ * (Cb * m ^ 4) + Cβ * (Cf * m ^ 2) * (Cb * m ^ 2) ≤ C * m ^ 4`. Establish `a1 : Ca * m ^ 2 ≤ Ca * m ^ 4` using `mul_le_mul_of_nonneg_left hs hCa`. Establish `a2 : Cβ * Cf * m ^ 2 ≤ Cβ * Cf * m ^ 4` using `mul_le_mul_of_nonneg_left hs (mul_nonneg hβ hCf)`. Establish `a3 : (Ca + Cβ * (Cf + Cb + Cf * Cb)) * m ^ 4 ≤ C * m ^ 4` using `mul_le_mul_of_nonneg_right hC1 h4`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hexp2 : Cb * m ^ 2 ≤ C * m ^ 2` using `mul_le_mul_of_nonneg_right hC2 (by positivity)`. Conclude with `mul_le_mul (Real.rpow_le_rpow_of_exponent_le hb hexp) (Real.rpow_le_rpow_of_exponent_le hx hexp2) (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hb0 _)`.
-/
theorem ptArith {b m Ca Cf Cb Cβ C x : ℝ} (hb : 1 ≤ b) (hm : 1 ≤ m) (hCa : 0 ≤ Ca) (hCf : 0 ≤ Cf) (_hCb : 0 ≤ Cb)
    (hβ : 0 ≤ Cβ) (hC1 : Ca + Cβ * (Cf + Cb + Cf * Cb) ≤ C) (hC2 : Cb ≤ C) (hx : 1 ≤ x) :
    b ^ (Ca * m ^ 2) * ((b ^ Cβ) ^ (Cf * m ^ 2) * ((b ^ Cβ) ^ (Cb * m ^ 4) *
      ((b ^ Cβ) ^ (Cf * m ^ 2) * x) ^ (Cb * m ^ 2))) ≤ b ^ (C * m ^ 4) * x ^ (C * m ^ 2) := by
  have hb0 : 0 ≤ b := by linarith
  have hbp : 0 < b := by linarith
  have hx0 : 0 ≤ x := by linarith
  have e1 : (b ^ Cβ) ^ (Cf * m ^ 2) = b ^ (Cβ * (Cf * m ^ 2)) := (Real.rpow_mul hb0 _ _).symm
  have e2 : (b ^ Cβ) ^ (Cb * m ^ 4) = b ^ (Cβ * (Cb * m ^ 4)) := (Real.rpow_mul hb0 _ _).symm
  have e3 : (b ^ (Cβ * (Cf * m ^ 2)) * x) ^ (Cb * m ^ 2) =
      b ^ (Cβ * (Cf * m ^ 2) * (Cb * m ^ 2)) * x ^ (Cb * m ^ 2) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hb0 _) hx0, ← Real.rpow_mul hb0]
  rw [e1, e2, e3]
  have e4 : b ^ (Ca * m ^ 2) * (b ^ (Cβ * (Cf * m ^ 2)) * (b ^ (Cβ * (Cb * m ^ 4)) *
      (b ^ (Cβ * (Cf * m ^ 2) * (Cb * m ^ 2)) * x ^ (Cb * m ^ 2)))) =
      b ^ (Ca * m ^ 2 + Cβ * (Cf * m ^ 2) + Cβ * (Cb * m ^ 4) + Cβ * (Cf * m ^ 2) * (Cb * m ^ 2)) * x ^ (Cb * m ^ 2) := by
    rw [Real.rpow_add hbp, Real.rpow_add hbp, Real.rpow_add hbp]; ring
  rw [e4]
  have hs1 : 1 ≤ m ^ 2 := by nlinarith
  have hs : m ^ 2 ≤ m ^ 4 := by nlinarith
  have h4 : 0 ≤ m ^ 4 := by positivity
  have hexp : Ca * m ^ 2 + Cβ * (Cf * m ^ 2) + Cβ * (Cb * m ^ 4) + Cβ * (Cf * m ^ 2) * (Cb * m ^ 2) ≤ C * m ^ 4 := by
    have a1 : Ca * m ^ 2 ≤ Ca * m ^ 4 := mul_le_mul_of_nonneg_left hs hCa
    have a2 : Cβ * Cf * m ^ 2 ≤ Cβ * Cf * m ^ 4 := mul_le_mul_of_nonneg_left hs (mul_nonneg hβ hCf)
    have a3 : (Ca + Cβ * (Cf + Cb + Cf * Cb)) * m ^ 4 ≤ C * m ^ 4 := mul_le_mul_of_nonneg_right hC1 h4
    nlinarith
  have hexp2 : Cb * m ^ 2 ≤ C * m ^ 2 := mul_le_mul_of_nonneg_right hC2 (by positivity)
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hb hexp) (Real.rpow_le_rpow_of_exponent_le hx hexp2)
    (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hb0 _)

/- English proof (translation)
Use `AuxiliaryNormPrimes.partial_trace_of_frames D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Ca Ch Cf Cs Cs' Cβ Cb C hAmp hFr hStd hTF (gfOfRelPt D) h47 hβ hCb (fun x hx => ?_)` and prove the remaining obligations. Establish `hb : 1 ≤ large₂.sc.b`. Unfold `Scale.b`. Conclude with `Real.one_le_exp (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one large₂.sc.one_lt_alt)) _)`. Establish `hm : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast le_trans (by norm_num) D.R.two_le_m`.

Conclude with `ptArith hb hm hCa hCf hCb (by linarith) hC1 hC2 hx`.
-/
theorem AuxiliaryNormPrimes.plancherelBoundOneParameter_of_uniformity (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 Ca Ch Cf Cs Cs' Cβ Cb C : ℝ)
    (hAmp : AmpIsBessel D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Ca) (hFr : FrameChange D Ch Cs Cn Cf)
    (hStd : StdOfHyp D large₂ C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ) (hTF : TFrameOfHyp D large₂ C' Cl Cg cb Cu cT CT C0)
    (h47 : OnePlaceEstimates.UniformityTheoremBPrime D Ch Cn Cs Cs' Cb) (hβ : 1 ≤ Cβ) (hCb : 0 ≤ Cb) (hCa : 0 ≤ Ca) (hCf : 0 ≤ Cf)
    (hC1 : Ca + Cβ * (Cf + Cb + Cf * Cb) ≤ C) (hC2 : Cb ≤ C) :
    AuxiliaryNormPrimes.PlancherelBoundOneParameter D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  refine AuxiliaryNormPrimes.partial_trace_of_frames D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Ca Ch Cf Cs Cs' Cβ Cb C hAmp hFr hStd hTF (gfOfRelPt D) h47 hβ hCb (fun x hx => ?_)
  have hb : 1 ≤ large₂.sc.b := by
    unfold Scale.b
    exact Real.one_le_exp (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one large₂.sc.one_lt_alt)) _)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast le_trans (by norm_num) D.R.two_le_m
  exact ptArith hb hm hCa hCf hCb (by linarith) hC1 hC2 hx

/- English proof (translation)
Establish `hb0 : 0 ≤ b` using `by linarith`. Establish `hB2 : 2 ≤ b ^ Cβ` using `le_trans (by`. Use `Real.add_one_le_exp (1 : ℝ)` as an intermediate fact. Use the proof step `linarith) hB`. Establish `hBp : 0 < b ^ Cβ` using `by linarith`.

Establish `hBc : 1 ≤ (b ^ Cβ) ^ Ch` using `Real.one_le_rpow (by linarith) hCh`. Establish `h1 : 1 + 1 / ka ≤ (b ^ Cβ) ^ (Ch + 1)`. Rewrite using `[Real.rpow_add hBp, Real.rpow_one]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hpos : 0 ≤ 1 + 1 / ka` using `by positivity`.

Establish `h2 : (1 + 1 / ka) ^ n ≤ ((b ^ Cβ) ^ (Ch + 1)) ^ n` using `pow_le_pow_left₀ hpos h1 n`. Establish `h3 : ((b ^ Cβ) ^ (Ch + 1)) ^ n = (b ^ Cβ) ^ ((Ch + 1) * (n : ℝ))`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hBp.le]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← h3]`.

Conclude with `mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hBp.le _)`. Use `_ = b ^ (Cβ * (C2 + Ch + 1) * m) := by`. Rewrite using `[← Real.rpow_add hBp, ← Real.rpow_mul hb0, hm]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ b ^ (C * m) := Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right hC (by rw [← hm]; exact Nat.cast_nonneg _))`.
-/
theorem momArith {b Cβ C2 Ch C ka m : ℝ} {n : ℕ} (hb : 1 ≤ b) (hB : Real.exp 1 ≤ b ^ Cβ) (hCh : 0 ≤ Ch) (hka0 : 0 < ka)
    (hka : 1 / ka ≤ (b ^ Cβ) ^ Ch) (hm : (n : ℝ) = m) (hC : Cβ * (C2 + Ch + 1) ≤ C) :
    (b ^ Cβ) ^ (C2 * (n : ℝ)) * (1 + 1 / ka) ^ n ≤ b ^ (C * m) := by
  have hb0 : 0 ≤ b := by linarith
  have hB2 : 2 ≤ b ^ Cβ := le_trans (by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith) hB
  have hBp : 0 < b ^ Cβ := by linarith
  have hBc : 1 ≤ (b ^ Cβ) ^ Ch := Real.one_le_rpow (by linarith) hCh
  have h1 : 1 + 1 / ka ≤ (b ^ Cβ) ^ (Ch + 1) := by
    rw [Real.rpow_add hBp, Real.rpow_one]
    nlinarith
  have hpos : 0 ≤ 1 + 1 / ka := by positivity
  have h2 : (1 + 1 / ka) ^ n ≤ ((b ^ Cβ) ^ (Ch + 1)) ^ n := pow_le_pow_left₀ hpos h1 n
  have h3 : ((b ^ Cβ) ^ (Ch + 1)) ^ n = (b ^ Cβ) ^ ((Ch + 1) * (n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hBp.le]
  calc (b ^ Cβ) ^ (C2 * (n : ℝ)) * (1 + 1 / ka) ^ n
      ≤ (b ^ Cβ) ^ (C2 * (n : ℝ)) * (b ^ Cβ) ^ ((Ch + 1) * (n : ℝ)) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hBp.le _)
    _ = b ^ (Cβ * (C2 + Ch + 1) * m) := by
        rw [← Real.rpow_add hBp, ← Real.rpow_mul hb0, hm]; congr 1; ring
    _ ≤ b ^ (C * m) := Real.rpow_le_rpow_of_exponent_le hb
        (mul_le_mul_of_nonneg_right hC (by rw [← hm]; exact Nat.cast_nonneg _))

/- English proof (translation)
Introduce `hH τ w w' hTT θ hθ W hW lam' hl A hA a q hq`. Establish `hC : (large₂.sc.b ^ Cβ) ^ (C2 * ((2 * D.R.rS + 2 : ℕ) : ℝ)) * (1 + 1 / kaS D) ^ (2 * D.R.rS + 2) ≤ large₂.sc.b ^ (C * (D.R.m : ℝ))`. Establish `hm : ((2 * D.R.rS + 2 : ℕ) : ℝ) = (D.R.m : ℝ)`. Establish `h1` using `dimS_eq D.R`. Establish `h2` using `D.R.two_le_m`.

Unfold `Ranks.r at h1`. Establish `h3 : 2 * D.R.rS + 2 = D.R.m` using `by omega`. Conclude with `h3` after adjusting the coercions. Establish `hb1 : 1 ≤ large₂.sc.b`. Unfold `Scale.b`.

Conclude with `Real.one_le_exp (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one large₂.sc.one_lt_alt)) _)`. Conclude with `momArith hb1 (exp_one_le_b_rpow large₂ hβ) hCh (hStd hH τ w w').1.2.2.2.1 (by rw [one_div]; exact (hStd hH τ w w').1.2.2.2.2.2.1) hm hC0`. Establish `hT : 0 < Tr D w` using `Nat.cast_pos.2 hTT.1.pos`. Establish `hT' : 0 < Tr D w'` using `Nat.cast_pos.2 hTT.2.1.pos`. Establish `hb0 : 0 < large₂.sc.b` using `Real.exp_pos _`.

Take `⟨hStd1, -⟩` from `hStd hH τ w w'`. Establish `hka : 0 < kaS D` using `hStd1.2.2.2.1`. Establish `hTzW : Tz D.R.k D.R.rS W.z = Tr D w` using `hW.2.2.2.2.1`. Establish `hTzW' : Tz D.R.k D.R.rS W.z' = Tr D w'` using `hW.2.2.2.2.2.1`. Take `⟨Bf, P, w0, hBf, hnorm, hP, hw0, hw0ne, hid⟩` from `hMom hH τ w w' θ W hW lam' hl A hA hT hT'`.

Take `⟨bv, hbv, hShape, hrange⟩` from `hRg hH τ w`. Take `⟨hr1, hr2⟩` from `hrange lam' q hl hq`. Establish `h1k : 1 ≤ D.R.k`. Establish `h1 : D.R.m ^ 4 ≤ D.R.f` using `hH.1.2.2.1`. Establish `h2 : D.R.f ≤ D.R.k` using `hH.1.2.2.2.1`.

Establish `h3 : 1 ≤ D.R.m ^ 4` using `Nat.one_le_pow _ _ (lt_of_lt_of_le (by norm_num) D.R.two_le_m)`. Use linear arithmetic over natural numbers and integers. Establish `hgg : 0 ≤ gg D` using `by unfold gg; positivity`. Establish `hka0 : 0 < D.host.ka`. Assume the negation of the conclusion as `h`.

Conclude with `absurd hka (not_lt.2 (div_nonpos_of_nonpos_of_nonneg (not_lt.1 h) hgg))`. Establish `hv : 0 < D.host.v`. Unfold `Host.ka at hka0`. Assume the negation of the conclusion as `h`. Conclude with `absurd hka0 (not_lt.2 (div_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (not_lt.1 h)))`.

Establish `hθ0 : 0 < θ` using `lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ.1`. Establish `hκ : 0 < kapN D θ`. Unfold `kapN`. Conclude with `ENNReal.ofReal_pos.2 (mul_pos (Real.rpow_pos_of_pos (by positivity) _) hθ0)`. Establish `e0 : (kaS D / kaS D) ^ (2 * D.R.rS) = 1` using `by rw [div_self hka.ne', one_pow]`.

Establish `hLoc : LocOk D Ch Cs (toBesselK D τ w w' θ W lam' A hW hA hT hT') (lamD D τ) (kaS D) (large₂.sc.b ^ Cβ) (kaS D)`. Use `⟨h1k, rfl, rfl, hκ, ENNReal.ofReal_ne_top, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e0, mul_one, mul_one] show StdHyp Ch Cs D.R.k D.R.rS (epsSH D.R) (lamD D τ) (uS D w τ) (uS D w' τ) (Tz D.R.k D.R.rS W.z) (Tz D.R.k D.R.rS W.z') (kaS D) (large₂.sc.b ^ Cβ)`. Rewrite using `[hTzW, hTzW']`. Conclude with `hStd1`.

Use `show 1 ≤ Tz D.R.k D.R.rS W.z * kaS D ^ (2 * D.R.rS)`. Rewrite using `[hTzW]`. Conclude with `hTF hH w`. Use `show 1 ≤ Tz D.R.k D.R.rS W.z' * kaS D ^ (2 * D.R.rS)`. Rewrite using `[hTzW']`.

Conclude with `hTF hH w'`. Establish `h` using `h93 (toBesselK D τ w w' θ W lam' A hW hA hT hT') (lamD D τ) (kaS D) (large₂.sc.b ^ Cβ) bv Bf W.μG (muS W.μW W.μN) W.νS P w0 0 hLoc.to0 hbv hShape hBf hW.2.2.2.2.2.2.1 (hS τ w w' θ W hW) hW.2.2.2.2.2.2.2.2.2.2.2.2.1 hnorm hP (Or.inl hw0) hw0ne`. Establish `h4` using `((h.2.2.2 q hr1 hr2).1 a).1`. Establish `hF : Measurable (fun l : Fin (D.R.rS + 1) → ℝ => ENNReal.ofReal (l a ^ (2 * q)))` using `ENNReal.measurable_ofReal.comp ((measurable_pi_apply a).pow_const _)`. Establish `hid'` using `hid (fun l => ENNReal.ofReal (l a ^ (2 * q))) hF`.

Rewrite using `[hid', mul_comm]`. Use `mul_le_mul' (le_trans h4 (ENNReal.ofReal_le_ofReal ?_)) le_rfl` and prove the remaining obligations. Establish `hH1 : 0 ≤ (large₂.sc.b ^ Cβ) ^ (C2 * ((2 * D.R.rS + 2 : ℕ) : ℝ)) * (1 + 1 / kaS D) ^ (2 * D.R.rS + 2)`. Establish `: 0 < 1 / kaS D` using `by positivity`. Check the signs of the components of the expression.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hb0.le]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem AuxiliaryNormPrimes.moment_bound_of_frames (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq Ch Cs Cs' Cβ Cq0 Cr C2 C : ℝ)
    (hMom : MomNormR D large₂ C' Cl Cg cb Cu cT CT C0 Cn) (hS : MuSHaar D) (hStd : StdOfHyp D large₂ C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ)
    (hTF : TFrameOfHyp D large₂ C' Cl Cg cb Cu cT CT C0)
    (hRg : RangeOfHyp D large₂ C' Cl Cg cb Cu cT CT C0 Cs Cn Cq Cq0 Cr) (h93 : OnePlaceEstimates.SubmultiplicativeLocalNorm D Ch Cs Cq0 Cr C2)
    (hβ : 1 ≤ Cβ) (hCh : 0 ≤ Ch) (hC0 : Cβ * (C2 + Ch + 1) ≤ C) :
    AuxiliaryNormPrimes.ArchimedeanMomentBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C := by
  intro hH τ w w' hTT θ hθ W hW lam' hl A hA a q hq
  have hC : (large₂.sc.b ^ Cβ) ^ (C2 * ((2 * D.R.rS + 2 : ℕ) : ℝ)) * (1 + 1 / kaS D) ^ (2 * D.R.rS + 2) ≤
      large₂.sc.b ^ (C * (D.R.m : ℝ)) := by
    have hm : ((2 * D.R.rS + 2 : ℕ) : ℝ) = (D.R.m : ℝ) := by
      have h1 := dimS_eq D.R
      have h2 := D.R.two_le_m
      unfold Ranks.r at h1
      have h3 : 2 * D.R.rS + 2 = D.R.m := by omega
      exact_mod_cast h3
    have hb1 : 1 ≤ large₂.sc.b := by
      unfold Scale.b
      exact Real.one_le_exp (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one large₂.sc.one_lt_alt)) _)
    exact momArith hb1 (exp_one_le_b_rpow large₂ hβ) hCh (hStd hH τ w w').1.2.2.2.1
      (by rw [one_div]; exact (hStd hH τ w w').1.2.2.2.2.2.1) hm hC0
  have hT : 0 < Tr D w := Nat.cast_pos.2 hTT.1.pos
  have hT' : 0 < Tr D w' := Nat.cast_pos.2 hTT.2.1.pos
  have hb0 : 0 < large₂.sc.b := Real.exp_pos _
  obtain ⟨hStd1, -⟩ := hStd hH τ w w'
  have hka : 0 < kaS D := hStd1.2.2.2.1
  have hTzW : Tz D.R.k D.R.rS W.z = Tr D w := hW.2.2.2.2.1
  have hTzW' : Tz D.R.k D.R.rS W.z' = Tr D w' := hW.2.2.2.2.2.1
  obtain ⟨Bf, P, w0, hBf, hnorm, hP, hw0, hw0ne, hid⟩ := hMom hH τ w w' θ W hW lam' hl A hA hT hT'
  obtain ⟨bv, hbv, hShape, hrange⟩ := hRg hH τ w
  obtain ⟨hr1, hr2⟩ := hrange lam' q hl hq
  have h1k : 1 ≤ D.R.k := by
    have h1 : D.R.m ^ 4 ≤ D.R.f := hH.1.2.2.1
    have h2 : D.R.f ≤ D.R.k := hH.1.2.2.2.1
    have h3 : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (lt_of_lt_of_le (by norm_num) D.R.two_le_m)
    omega
  have hgg : 0 ≤ gg D := by unfold gg; positivity
  have hka0 : 0 < D.host.ka := by
    by_contra h
    exact absurd hka (not_lt.2 (div_nonpos_of_nonpos_of_nonneg (not_lt.1 h) hgg))
  have hv : 0 < D.host.v := by
    unfold Host.ka at hka0
    by_contra h
    exact absurd hka0 (not_lt.2 (div_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (not_lt.1 h)))
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ.1
  have hκ : 0 < kapN D θ := by
    unfold kapN
    exact ENNReal.ofReal_pos.2 (mul_pos (Real.rpow_pos_of_pos (by positivity) _) hθ0)
  have e0 : (kaS D / kaS D) ^ (2 * D.R.rS) = 1 := by rw [div_self hka.ne', one_pow]
  have hLoc : LocOk D Ch Cs (toBesselK D τ w w' θ W lam' A hW hA hT hT') (lamD D τ) (kaS D) (large₂.sc.b ^ Cβ) (kaS D) := by
    refine ⟨h1k, rfl, rfl, hκ, ENNReal.ofReal_ne_top, ?_, ?_, ?_⟩
    · rw [e0, mul_one, mul_one]
      show StdHyp Ch Cs D.R.k D.R.rS (epsSH D.R) (lamD D τ) (uS D w τ) (uS D w' τ) (Tz D.R.k D.R.rS W.z)
        (Tz D.R.k D.R.rS W.z') (kaS D) (large₂.sc.b ^ Cβ)
      rw [hTzW, hTzW']
      exact hStd1
    · show 1 ≤ Tz D.R.k D.R.rS W.z * kaS D ^ (2 * D.R.rS)
      rw [hTzW]; exact hTF hH w
    · show 1 ≤ Tz D.R.k D.R.rS W.z' * kaS D ^ (2 * D.R.rS)
      rw [hTzW']; exact hTF hH w'
  have h := h93 (toBesselK D τ w w' θ W lam' A hW hA hT hT') (lamD D τ) (kaS D) (large₂.sc.b ^ Cβ) bv Bf W.μG
    (muS W.μW W.μN) W.νS P w0 0 hLoc.to0 hbv hShape hBf hW.2.2.2.2.2.2.1 (hS τ w w' θ W hW)
    hW.2.2.2.2.2.2.2.2.2.2.2.2.1 hnorm hP (Or.inl hw0) hw0ne
  have h4 := ((h.2.2.2 q hr1 hr2).1 a).1
  have hF : Measurable (fun l : Fin (D.R.rS + 1) → ℝ => ENNReal.ofReal (l a ^ (2 * q))) :=
    ENNReal.measurable_ofReal.comp ((measurable_pi_apply a).pow_const _)
  have hid' := hid (fun l => ENNReal.ofReal (l a ^ (2 * q))) hF
  rw [hid', mul_comm]
  refine mul_le_mul' (le_trans h4 (ENNReal.ofReal_le_ofReal ?_)) le_rfl
  have hH1 : 0 ≤ (large₂.sc.b ^ Cβ) ^ (C2 * ((2 * D.R.rS + 2 : ℕ) : ℝ)) * (1 + 1 / kaS D) ^ (2 * D.R.rS + 2) := by
    have : 0 < 1 / kaS D := by positivity
    positivity
  calc ((large₂.sc.b ^ Cβ) ^ (C2 * ((2 * D.R.rS + 2 : ℕ) : ℝ)) * (1 + 1 / kaS D) ^ (2 * D.R.rS + 2)) ^ (2 * q)
      ≤ (large₂.sc.b ^ (C * (D.R.m : ℝ))) ^ (2 * q) := pow_le_pow_left₀ hH1 hC _
    _ = large₂.sc.b ^ (2 * C * D.R.m * q) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
        congr 1
        push_cast
        ring

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[epsI]`. Simplify using `[epsI, h]`.
-/
theorem epsI_singleton {N : ℕ} (i : Fin N) : epsI ({i} : Finset (Fin N)) = Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h; simp [epsI]
  · simp [epsI, h]

/- English proof (translation)
Unfold `l1dist`. Establish `h1 : ∑ a, |(Pi.single i (1 : ℝ) : Fin N → ℝ) a| = 1`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Simplify using `[hb]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum (fun a _ => ?_)` and prove the remaining obligations.

Establish `: (x - (Pi.single i (1 : ℝ) : Fin N → ℝ)) a - y a = (x a - y a) - (Pi.single i (1 : ℝ) : Fin N → ℝ) a`. Simplify using `only [Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `abs_sub _ _`.

Use `_ = ∑ a, |x a - y a| + 1 := by rw [Finset.sum_add_distrib, h1]`.
-/
theorem l1dist_sub_single {N : ℕ} (x y : Fin N → ℝ) (i : Fin N) :
    l1dist (x - Pi.single i 1) y ≤ l1dist x y + 1 := by
  unfold l1dist
  have h1 : ∑ a, |(Pi.single i (1 : ℝ) : Fin N → ℝ) a| = 1 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  calc ∑ a, |(x - (Pi.single i (1 : ℝ) : Fin N → ℝ)) a - y a| ≤ ∑ a, (|x a - y a| + |(Pi.single i (1 : ℝ) : Fin N → ℝ) a|) := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        have : (x - (Pi.single i (1 : ℝ) : Fin N → ℝ)) a - y a = (x a - y a) - (Pi.single i (1 : ℝ) : Fin N → ℝ) a := by
          simp only [Pi.sub_apply]; ring
        rw [this]
        exact abs_sub _ _
    _ = ∑ a, |x a - y a| + 1 := by rw [Finset.sum_add_distrib, h1]

/- English proof (translation)
Introduce `hH τ w w' hTT θ hθ W hW lam' hl A hA i s hs A' hA'`. Establish `key : ∀ (μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (B B' : LocS W), l1dist μ (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + 1 → GoodS D μ B → GoodS D (μ + Pi.single i 1) B' → (D.R.r : ℝ) ^ (-C) ≤ B'.deg / B.deg ∧ B'.deg / B.deg ≤ (D.R.r : ℝ) ^ C`. Introduce `μ B B' hμ hB hB'`. Take `⟨P, X, v, vs, hDS, hL2, hi, hv, hvs, hdeg⟩` from `hStep hH τ w w' hTT θ hθ W hW μ hμ B B' i hB hB'`. Rewrite using `[hdeg, h90 _ (epsSH D.R) μ B.H _ X hB.1 hDS hL2 i hi v vs hv hvs]`.

Conclude with `hProd hH τ μ hμ i`. Break down `hs with rfl | rfl` into its components or cases. Use `key lam' A A' (by linarith) hA ?_` and prove the remaining obligations. Rewrite using `[← epsI_singleton, ← one_smul ℝ (epsI {i})]`. Conclude with `hA'`.

Establish `hμ : l1dist (lam' - Pi.single i 1) (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + 1` using `le_trans (l1dist_sub_single _ _ _) (by linarith)`. Establish `e1 : lam' + (-1 : ℝ) • epsI {i} = lam' - Pi.single i 1`. Rewrite using `[epsI_singleton, neg_one_smul, sub_eq_add_neg]`. Establish `e2 : lam' - Pi.single i 1 + Pi.single i 1 = lam'` using `sub_add_cancel _ _`. Rewrite `hA'` using `[e1]`.

Take `⟨h1, h2⟩` from `key (lam' - Pi.single i 1) A' A hμ hA' (by rw [e2]; exact hA)`. Establish `hr : 0 < (D.R.r : ℝ)`. Establish `h3` using `D.R.two_le_m`. Establish `h4 : 0 < D.R.r` using `by unfold Ranks.r; omega`. Conclude with `h4` after adjusting the coercions.

Establish `hnC : 0 < (D.R.r : ℝ) ^ C` using `Real.rpow_pos_of_pos hr _`. Rewrite `h1`, the goal using `[Real.rpow_neg hr.le]`. Establish `hx : 0 < A.deg / A'.deg` using `lt_of_lt_of_le (inv_pos.2 hnC) h1`. Rewrite using `[← inv_div A.deg A'.deg]`. Use `⟨inv_anti₀ hx h2, ?_⟩` and prove the remaining obligations.

Establish `h5` using `inv_anti₀ (inv_pos.2 hnC) h1`. Rewrite `h5` using `[inv_inv]`. Then use the resulting hypothesis.
-/
theorem AuxiliaryNormPrimes.degree_ratio_unit_bound_of_formal_degree_ratio (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ)
    (hStep : DegStep D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1) (hProd : ProdBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C) (h90 : OnePlaceEstimates.FormalDegreeRatioAlt D) :
    AuxiliaryNormPrimes.DegreeRatioUnitStepBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro hH τ w w' hTT θ hθ W hW lam' hl A hA i s hs A' hA'
  have key : ∀ (μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (B B' : LocS W),
      l1dist μ (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + 1 → GoodS D μ B → GoodS D (μ + Pi.single i 1) B' →
      (D.R.r : ℝ) ^ (-C) ≤ B'.deg / B.deg ∧ B'.deg / B.deg ≤ (D.R.r : ℝ) ^ C := by
    intro μ B B' hμ hB hB'
    obtain ⟨P, X, v, vs, hDS, hL2, hi, hv, hvs, hdeg⟩ := hStep hH τ w w' hTT θ hθ W hW μ hμ B B' i hB hB'
    rw [hdeg, h90 _ (epsSH D.R) μ B.H _ X hB.1 hDS hL2 i hi v vs hv hvs]
    exact hProd hH τ μ hμ i
  rcases hs with rfl | rfl
  · refine key lam' A A' (by linarith) hA ?_
    rw [← epsI_singleton, ← one_smul ℝ (epsI {i})]
    exact hA'
  · have hμ : l1dist (lam' - Pi.single i 1) (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + 1 :=
      le_trans (l1dist_sub_single _ _ _) (by linarith)
    have e1 : lam' + (-1 : ℝ) • epsI {i} = lam' - Pi.single i 1 := by
      rw [epsI_singleton, neg_one_smul, sub_eq_add_neg]
    have e2 : lam' - Pi.single i 1 + Pi.single i 1 = lam' := sub_add_cancel _ _
    rw [e1] at hA'
    obtain ⟨h1, h2⟩ := key (lam' - Pi.single i 1) A' A hμ hA' (by rw [e2]; exact hA)
    have hr : 0 < (D.R.r : ℝ) := by
      have h3 := D.R.two_le_m
      have h4 : 0 < D.R.r := by unfold Ranks.r; omega
      exact_mod_cast h4
    have hnC : 0 < (D.R.r : ℝ) ^ C := Real.rpow_pos_of_pos hr _
    rw [Real.rpow_neg hr.le] at h1 ⊢
    have hx : 0 < A.deg / A'.deg := lt_of_lt_of_le (inv_pos.2 hnC) h1
    rw [← inv_div A.deg A'.deg]
    refine ⟨inv_anti₀ hx h2, ?_⟩
    have h5 := inv_anti₀ (inv_pos.2 hnC) h1
    rwa [inv_inv] at h5

/- English proof (translation)
Take `⟨_, _, _, hka, h1, h2, _, _, _, _, hl, _⟩` from `h`. Establish `hb0 : 0 ≤ b` using `le_trans (abs_nonneg _) (hl ⟨0, by omega⟩)`. Establish `h3 : 1 ≤ b ^ Ch`. Break down `le_total 1 ka with h | h` into its components or cases. Conclude with `le_trans h h1`.

Conclude with `le_trans ((one_le_inv₀ hka).2 h) h2`. Assume the negation of the conclusion as `hb`. Conclude with `absurd h3 (not_le.2 (Real.rpow_lt_one hb0 (not_le.1 hb) hCh))`.
-/
theorem one_le_b_of_StdHyp {Ch Cg : ℝ} {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {u u' : Fin k → ℝ} {T T' ka b : ℝ} (hCh : 0 < Ch) (h : StdHyp Ch Cg k r ε lam u u' T T' ka b) : 1 ≤ b := by
  obtain ⟨_, _, _, hka, h1, h2, _, _, _, _, hl, _⟩ := h
  have hb0 : 0 ≤ b := le_trans (abs_nonneg _) (hl ⟨0, by omega⟩)
  have h3 : 1 ≤ b ^ Ch := by
    rcases le_total 1 ka with h | h
    · exact le_trans h h1
    · exact le_trans ((one_le_inv₀ hka).2 h) h2
  by_contra hb
  exact absurd h3 (not_le.2 (Real.rpow_lt_one hb0 (not_le.1 hb) hCh))

/- English proof (translation)
Unfold `BpIneq at h ⊢`. Use `le_trans h (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul (Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right hle (by positivity))) (Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (mul_le_mul_of_nonneg_right hle (by positivity))) (Real.rpow_nonneg (le_trans z …` and prove the remaining obligations.
-/
theorem BpIneq_mono (D : D7) {Cb Cb' : ℝ} (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) {b : ℝ} (γ : Point ℂ (D.R.rS + 1)) (hb : 1 ≤ b)
    (hle : Cb ≤ Cb') (h : BpIneq D Cb L f μsec b γ) : BpIneq D Cb' L f μsec b γ := by
  unfold BpIneq at h ⊢
  refine le_trans h (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul
    (Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right hle (by positivity)))
    (Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (mul_le_mul_of_nonneg_right hle (by positivity)))
    (Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _) (Real.rpow_nonneg (by linarith) _))) le_rfl)

/- English proof (translation)
Introduce `L lam0 f μsec ka b hLoc hR hf hμ hN γ hG` and use `BpIneq_mono D L f μsec γ (one_le_b_of_StdHyp hCh hLoc.2.2.2.2.2.1) hle (h L lam0 f μsec ka b hLoc hR hf hμ hN γ hG)`.
-/
theorem OnePlaceEstimates.upper_bound_mono_constant (D : D7) {Ch Cu Cg Cg' Cb Cb' : ℝ} (hCh : 0 < Ch) (hle : Cb ≤ Cb')
    (h : OnePlaceEstimates.UniformityTheoremBPrime D Ch Cu Cg Cg' Cb) : OnePlaceEstimates.UniformityTheoremBPrime D Ch Cu Cg Cg' Cb' :=
  fun L lam0 f μsec ka b hLoc hR hf hμ hN γ hG =>
    BpIneq_mono D L f μsec γ (one_le_b_of_StdHyp hCh hLoc.2.2.2.2.2.1) hle (h L lam0 f μsec ka b hLoc hR hf hμ hN γ hG)

section BridgeFam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cg cb Cu cT CT C0 C1 : ℝ)

/- English proof (translation)
Use `⟨max (Ca + Cβ * (Cf + max Cb 0 + Cf * max Cb 0)) (max Cb 0), fun Cn => ?_⟩` and prove the remaining obligations. Take `⟨a, Cs', h⟩` from `h47 Cn`. Take `⟨a', h'⟩` from `hFr Cn`. Conclude with `Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i H => AuxiliaryNormPrimes.plancherelBoundOneParameter_of_uniformity _ _ _ _ _ _ _ _ _ _ Cn C1 Ca Ch Cf (max a a') Cs' Cβ (max Cb 0) _ H.1.1 (h' _ (le_max_right _ _) x i) H.1.2 H.2 (OnePlaceEstimates.upper_bound_mono_constant _ hCh …`.
-/
theorem AuxiliaryNormPrimes.familyPlancherelOneParameter_of_frames (Ch Cβ Ca Cf Cb : ℝ) (hCh : 0 < Ch) (hβ : 1 ≤ Cβ) (hCa : 0 ≤ Ca) (hCf : 0 ≤ Cf)
    (h47 : ∀ Cn, ∃ Cs₀ Cs', ∀ Cs ≥ Cs₀, OnePlaceEstimates.FamilyUniformityTheoremBPrime Fm Ch Cn Cs Cs' Cb)
    (hAmp : ∀ Cn, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i => AmpIsBessel (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 Ca)
    (hFr : ∀ Cn, ∃ Cs₀, ∀ Cs ≥ Cs₀, ∀ x (i : Fm.Ix x), FrameChange (Fm.D x i) Ch Cs Cn Cf)
    (hStd : ∀ Cs Cs', Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i =>
      StdOfHyp (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ)
    (hTF : Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i => TFrameOfHyp (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0) :
    AuxiliaryNormPrimes.FamilyPlancherelOneParameter Fm Cg cb Cu cT CT C0 C1 := by
  refine ⟨max (Ca + Cβ * (Cf + max Cb 0 + Cf * max Cb 0)) (max Cb 0), fun Cn => ?_⟩
  obtain ⟨a, Cs', h⟩ := h47 Cn
  obtain ⟨a', h'⟩ := hFr Cn
  exact Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i H =>
    AuxiliaryNormPrimes.plancherelBoundOneParameter_of_uniformity _ _ _ _ _ _ _ _ _ _ Cn C1 Ca Ch Cf (max a a') Cs' Cβ (max Cb 0) _ H.1.1 (h' _ (le_max_right _ _) x i) H.1.2 H.2
      (OnePlaceEstimates.upper_bound_mono_constant _ hCh (le_max_left _ _) (h _ (le_max_left _ _) x i)) hβ (le_max_right _ _)
      hCa hCf (le_max_left _ _) (le_max_right _ _)) (((hAmp Cn).and (hStd (max a a') Cs')).and hTF)

/- English proof (translation)
Introduce `Cq`. Use `⟨Cβ * (C2 + Ch + 1), fun Cn => ?_⟩` and prove the remaining obligations. Conclude with `Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i H => AuxiliaryNormPrimes.moment_bound_of_frames _ _ _ _ _ _ _ _ _ _ Cn C1 Cq Ch Cs 0 Cβ Cq0 Cr C2 _ H.2 (hS x i) H.1.1.1 H.1.1.2 H.1.2 (h93 x i) hβ hCh le_rfl) ((((hStd Cs 0).and hTF).and (hRg Cn Cq)).and (hMom Cg cb Cu cT CT C0 C …`.
-/
theorem AuxiliaryNormPrimes.family_moment_of_frames (Ch Cβ Cs Cq0 Cr C2 : ℝ) (hCh : 0 ≤ Ch) (hβ : 1 ≤ Cβ) (h93 : OnePlaceEstimates.FamilySubmultiplicativeNorm Fm Ch Cs Cq0 Cr C2)
    (hMom : ∀ Cg cb Cu cT CT C0 : ℝ, ∀ Cn, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i =>
      MomNormR (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn) (hS : ∀ x (i : Fm.Ix x), MuSHaar (Fm.D x i))
    (hStd : ∀ Cs Cs', Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i =>
      StdOfHyp (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ)
    (hTF : Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i => TFrameOfHyp (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0)
    (hRg : ∀ Cn Cq, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i =>
      RangeOfHyp (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cs Cn Cq Cq0 Cr) :
    AuxiliaryNormPrimes.FamilyArchimedeanMomentBound Fm Cg cb Cu cT CT C0 C1 := by
  intro Cq
  refine ⟨Cβ * (C2 + Ch + 1), fun Cn => ?_⟩
  exact Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i H =>
    AuxiliaryNormPrimes.moment_bound_of_frames _ _ _ _ _ _ _ _ _ _ Cn C1 Cq Ch Cs 0 Cβ Cq0 Cr C2 _ H.2 (hS x i) H.1.1.1 H.1.1.2 H.1.2 (h93 x i) hβ hCh le_rfl)
    ((((hStd Cs 0).and hTF).and (hRg Cn Cq)).and (hMom Cg cb Cu cT CT C0 Cn))

/- English proof (translation)
Assemble the required witnesses or components as `⟨C, fun Cn => Formalism.MainNotions.S.OwnEv.mono (fun _ _ x i H => AuxiliaryNormPrimes.degree_ratio_unit_bound_of_formal_degree_ratio _ _ _ _ _ _ _ _ _ _ Cn C1 C H.1 H.2 (h90 x i)) ((hStep Cn).and (hProd Cn))⟩`.
-/
theorem AuxiliaryNormPrimes.family_degree_ratio_unit_of_degree_and_prodBound (C : ℝ) (h90 : OnePlaceEstimates.FamilyBesselFormulas Fm)
    (hStep : ∀ Cn, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i => DegStep (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1)
    (hProd : ∀ Cn, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i => ProdBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C) :
    AuxiliaryNormPrimes.FamilyDegreeRatioUnitStep Fm Cg cb Cu cT CT C0 C1 :=
  ⟨C, fun Cn => Formalism.MainNotions.S.OwnEv.mono (fun _ _ x i H => AuxiliaryNormPrimes.degree_ratio_unit_bound_of_formal_degree_ratio _ _ _ _ _ _ _ _ _ _ Cn C1 C H.1 H.2 (h90 x i))
    ((hStep Cn).and (hProd Cn))⟩

end BridgeFam

end Bridge

section Assembly
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

/- English proof (translation)
The claim follows from `|D.what₂.Dstar / (D.duS w : ℝ) - ∏ τ, (Formalism.MainNotions.S.Tcrit D w τ / Formalism.MainNotions.S.Tr D w) ^ D.R.k| ≤ δ * ∏ τ, (Formalism.MainNotions.S.Tcrit D w τ / Formalism.MainNotions.S.Tr D w) ^ D.R.k := by refine le_trans (tprod_of_27 D h w) (mul_le_mul_of_nonneg_right hδ …`.
-/
theorem tprod_mono (D : D7) (h : LocalBesselAndTopKernel.projection_sandwich_lattice D) {δ : ℝ} (hδ : epsT D ≤ δ) (w : D.what₂.Word) :
    |D.what₂.Dstar / (D.duS w : ℝ) - ∏ τ, (Formalism.MainNotions.S.Tcrit D w τ / Formalism.MainNotions.S.Tr D w) ^ D.R.k| ≤
      δ * ∏ τ, (Formalism.MainNotions.S.Tcrit D w τ / Formalism.MainNotions.S.Tr D w) ^ D.R.k := by
  refine le_trans (tprod_of_27 D h w) (mul_le_mul_of_nonneg_right hδ ?_)
  have hDs : 0 < D.what₂.Dstar := by rw [← D.Dstar_eq w]; exact (D.mem w).A.Dstar_pos
  have hQ : 0 ≤ D.what₂.Dstar / (D.duS w : ℝ) := div_nonneg hDs.le (Nat.cast_nonneg _)
  have h2 := (h w).2
  by_contra hn
  have hn' := not_le.1 hn
  have := mul_neg_of_pos_of_neg (Real.exp_pos ((D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k))) hn'
  linarith

def EpsTF (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  ∀ δ > 0, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i =>
    Formalism.MainNotions.S.Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → epsT (Fm.D x i) ≤ δ

/- English proof (translation)
Introduce `δ hδ` and use `Formalism.MainNotions.S.OwnEv.mono (fun _ _ _ _ H hH w => tprod_mono _ (H.1 ⟨hH.2.1, hH.1, hH.2.2⟩) (H.2 hH) w) (Formalism.MainNotions.S.OwnEv.and (P := fun C' Cl x i => LocalBesselAndTopKernel.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT → LocalBesselAndTopKernel.projection …`.
-/
theorem AuxiliaryNormPrimes.family_temperature_product_asymptotic_of_bessel_bound (Cg cb Cu cT CT C0 : ℝ) (h27 : LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT) (hE : EpsTF Fm Cg cb Cu cT CT C0) :
    AuxiliaryNormPrimes.FamilyTemperatureProductAsymptotic Fm Cg cb Cu cT CT C0 := fun δ hδ =>
  Formalism.MainNotions.S.OwnEv.mono (fun _ _ _ _ H hH w => tprod_mono _ (H.1 ⟨hH.2.1, hH.1, hH.2.2⟩) (H.2 hH) w)
    (Formalism.MainNotions.S.OwnEv.and (P := fun C' Cl x i => LocalBesselAndTopKernel.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT → LocalBesselAndTopKernel.projection_sandwich_lattice (Fm.D x i)) h27
      (hE δ hδ))

/- English proof (translation)
Assemble the required witnesses or components as `⟨h1, h2, h3⟩`.
-/
theorem VanishingOnXAndXPlusGlobal.AdmF_of (h1 : VanishingOnXAndXPlusGlobal.admF1 Fm) (h2 : VanishingOnXAndXPlusGlobal.admF2) (h3 : VanishingOnXAndXPlusGlobal.admF3 Fm) : VanishingOnXAndXPlusGlobal.AdmF Fm := ⟨h1, h2, h3⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun x i => VanishingOnXAndXPlusGluing.gluing_contains_setting _ (h1 x i), fun _ _ => h2, h3⟩`.
-/
theorem VanishingOnXAndXPlusGluing.AdmF_of (h1 : VanishingOnXAndXPlusGlobal.admF1 Fm) (h2 : VanishingOnXAndXPlusGlobal.admF2) (h3 : VanishingOnXAndXPlusGlobal.admF3 Fm) : VanishingOnXAndXPlusGluing.AdmF Fm :=
  ⟨fun x i => VanishingOnXAndXPlusGluing.gluing_contains_setting _ (h1 x i), fun _ _ => h2, h3⟩

/- English proof (translation)
Introduce `Cg cb Cu cT CT C0` and use `⟨hPT Cg cb Cu cT CT C0, hDl Cg cb Cu cT CT C0, hMOM Cg cb Cu cT CT C0, hTl Cg cb Cu cT CT C0, hmult, hhad, hJ90 Cg cb Cu cT CT C0, hJ90p Cg cb Cu cT CT C0, hSchur Cg cb Cu cT CT C0, hWeyl⟩`.
-/
theorem VanishingOnXAndXPlusBranching.AdmF_of (C1 : ℝ)
    (hPT : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyPlancherelOneParameter Fm Cg cb Cu cT CT C0 C1) (hMOM : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyArchimedeanMomentBound Fm Cg cb Cu cT CT C0 C1)
    (hJ90p : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyDegreeRatioUnitStep Fm Cg cb Cu cT CT C0 C1)
    (hmult : AuxiliaryNormPrimes.UnitaryBranchingMultiplicityOne) (hhad : AuxiliaryNormPrimes.HadamardDeterminantInequality) (hWeyl : VanishingOnXAndXPlusBranching.FamilyTwelfthHypothesis Fm)
    (hDl : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyPlancherelDifferenceOperator Fm Cg cb Cu cT CT C0 C1) (hTl : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyCriticalTemperatureLower Fm Cg cb Cu cT CT C0)
    (hJ90 : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyBesselDegreeNormalization Fm Cg cb Cu cT CT C0 C1) (hSchur : ∀ Cg cb Cu cT CT C0, VanishingOnXAndXPlusBranching.FamilyWeylAndVandermonde Fm Cg cb Cu cT CT C0 C1) :
    VanishingOnXAndXPlusBranching.AdmF Fm C1 := fun Cg cb Cu cT CT C0 =>
  ⟨hPT Cg cb Cu cT CT C0, hDl Cg cb Cu cT CT C0, hMOM Cg cb Cu cT CT C0, hTl Cg cb Cu cT CT C0, hmult, hhad, hJ90 Cg cb Cu cT CT C0, hJ90p Cg cb Cu cT CT C0, hSchur Cg cb Cu cT CT C0, hWeyl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hM1, hM2, hmult, hhad, ha1, ha3, htr, hmk, hMV, fun Cg cb Cu cT CT C0 A C1 => ⟨hSW Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.family_temperature_product_asymptotic_of_bessel_bound Fm Cg cb Cu cT CT C0 (h27 Cg cb Cu cT CT C0) (hE Cg cb Cu cT CT C0), hTl Cg cb Cu cT CT C0, hPT Cg cb …`.
-/
theorem VanishingOnXAndXPlusMass.AdmF_of
    (ha1 : VanishingOnXAndXPlusGlobal.ConclusionF1 Fm) (ha3 : VanishingOnXAndXPlusGlobal.ConclusionF3 Fm) (hc1 : ∀ Cg cb Cu cT CT C0 C1, VanishingOnXAndXPlusBranching.ConclusionF1 Fm Cg cb Cu cT CT C0 C1)
    (h27 : ∀ Cg cb Cu cT CT C0, LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT)
    (hPT : ∀ Cg cb Cu cT CT C0 C1, AuxiliaryNormPrimes.FamilyPlancherelOneParameter Fm Cg cb Cu cT CT C0 C1) (hMOM : ∀ Cg cb Cu cT CT C0 C1, AuxiliaryNormPrimes.FamilyArchimedeanMomentBound Fm Cg cb Cu cT CT C0 C1)
    (hJ90p : ∀ Cg cb Cu cT CT C0 C1, AuxiliaryNormPrimes.FamilyDegreeRatioUnitStep Fm Cg cb Cu cT CT C0 C1)
    (hM1 : AuxiliaryNormPrimes.SecondSizeStatement Fm) (hMV : AuxiliaryNormPrimes.FamilyGaugeMassVolumes Fm)
    (hM2 : AuxiliaryNormPrimes.BesselFormLine Fm) (hmult : AuxiliaryNormPrimes.UnitaryBranchingMultiplicityOne) (hhad : AuxiliaryNormPrimes.HadamardDeterminantInequality) (htr : AuxiliaryNormPrimes.BanaszczykTransferenceBound) (hmk : AuxiliaryNormPrimes.MinkowskiFiniteSubgroupOrder)
    (hSW : ∀ Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.LocalGenericDensity Fm Cg cb Cu cT CT C0 A) (hForm : ∀ Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.FamilyFormulaUnderLoopData Fm Cg cb Cu cT CT C0 A)
    (hE : ∀ Cg cb Cu cT CT C0, EpsTF Fm Cg cb Cu cT CT C0) (hTl : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyCriticalTemperatureLower Fm Cg cb Cu cT CT C0)
    (hSum : ∀ Cg cb Cu cT CT C0 C1, AuxiliaryNormPrimes.FamilyPlancherelFiniteSums Fm Cg cb Cu cT CT C0 C1) (hDl : ∀ Cg cb Cu cT CT C0 C1, AuxiliaryNormPrimes.FamilyPlancherelDifferenceOperator Fm Cg cb Cu cT CT C0 C1)
    (hJ90 : ∀ Cg cb Cu cT CT C0 C1, AuxiliaryNormPrimes.FamilyBesselDegreeNormalization Fm Cg cb Cu cT CT C0 C1) :
    VanishingOnXAndXPlusMass.AdmF Fm :=
  ⟨hM1, hM2, hmult, hhad, ha1, ha3, htr, hmk, hMV, fun Cg cb Cu cT CT C0 A C1 =>
    ⟨hSW Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.family_temperature_product_asymptotic_of_bessel_bound Fm Cg cb Cu cT CT C0 (h27 Cg cb Cu cT CT C0) (hE Cg cb Cu cT CT C0), hTl Cg cb Cu cT CT C0, hPT Cg cb Cu cT CT C0 C1, hSum Cg cb Cu cT CT C0 C1,
      hDl Cg cb Cu cT CT C0 C1, hMOM Cg cb Cu cT CT C0 C1, hJ90 Cg cb Cu cT CT C0 C1, hJ90p Cg cb Cu cT CT C0 C1, hc1 Cg cb Cu cT CT C0 C1, hForm Cg cb Cu cT CT C0 A⟩⟩

variable (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.S.TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    Formalism.MainNotions.S.LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

/- English proof (translation)
Assemble the required witnesses or components as `⟨hM1, hM2, hMV, hmult, hhad, htr, hmk, hWeyl, VanishingOnXAndXPlus.family_hermitian_words_of_source Fm ha.2.1, VanishingOnXAndXPlus.family_gluing_twelve_of_setting Fm ha.2.2.1, VanishingOnXAndXPlus.family_size_bounds_of_source Fm ha.2.2.2.1, VanishingOnXAndXPlus.family_gluing_fou …`.
-/
theorem VanishingOnXAndXPlus.AdmF_of
    (ha : VanishingOnXAndXPlusGlobal.ConclusionOnFamily Fm) (hb : VanishingOnXAndXPlusMass.ConclusionOnFamily Fm) (hc : VanishingOnXAndXPlusBranching.OrbitValuationBound Fm C1)
    (h27 : ∀ Cg cb Cu cT CT C0, LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT)
    (hPT : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyPlancherelOneParameter Fm Cg cb Cu cT CT C0 C1) (hMOM : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyArchimedeanMomentBound Fm Cg cb Cu cT CT C0 C1)
    (hJ90p : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyDegreeRatioUnitStep Fm Cg cb Cu cT CT C0 C1)
    (hM1 : AuxiliaryNormPrimes.SecondSizeStatement Fm) (hMV : AuxiliaryNormPrimes.FamilyGaugeMassVolumes Fm)
    (hM2 : AuxiliaryNormPrimes.BesselFormLine Fm) (hmult : AuxiliaryNormPrimes.UnitaryBranchingMultiplicityOne) (hhad : AuxiliaryNormPrimes.HadamardDeterminantInequality) (htr : AuxiliaryNormPrimes.BanaszczykTransferenceBound) (hmk : AuxiliaryNormPrimes.MinkowskiFiniteSubgroupOrder)
    (hSW : ∀ Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.LocalGenericDensity Fm Cg cb Cu cT CT C0 A) (hForm : ∀ Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.FamilyFormulaUnderLoopData Fm Cg cb Cu cT CT C0 A)
    (hE : ∀ Cg cb Cu cT CT C0, EpsTF Fm Cg cb Cu cT CT C0) (hTl : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyCriticalTemperatureLower Fm Cg cb Cu cT CT C0)
    (hSum : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyPlancherelFiniteSums Fm Cg cb Cu cT CT C0 C1) (hDl : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyPlancherelDifferenceOperator Fm Cg cb Cu cT CT C0 C1)
    (hJ90 : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyBesselDegreeNormalization Fm Cg cb Cu cT CT C0 C1) (hHH : ∀ Cg cb Cu cT CT C0 A, VanishingOnXAndXPlus.FamilyTermMassEstimate Fm Cg cb Cu cT CT C0 A)
    (hVol : ∀ Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.FamilyTermVolumeBound Fm C1 X Y Cg cb Cu cT CT C0 A)
    (hWeyl : VanishingOnXAndXPlusBranching.FamilyTwelfthHypothesis Fm) (hSchur : ∀ Cg cb Cu cT CT C0, VanishingOnXAndXPlusBranching.FamilyWeylAndVandermonde Fm Cg cb Cu cT CT C0 C1)
    (hWeylU : ∀ Cg cb Cu cT CT C0, VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0) :
    VanishingOnXAndXPlus.AdmF Fm C1 X Y :=
  ⟨hM1, hM2, hMV, hmult, hhad, htr, hmk, hWeyl, VanishingOnXAndXPlus.family_hermitian_words_of_source Fm ha.2.1, VanishingOnXAndXPlus.family_gluing_twelve_of_setting Fm ha.2.2.1,
    VanishingOnXAndXPlus.family_size_bounds_of_source Fm ha.2.2.2.1, VanishingOnXAndXPlus.family_gluing_fourteen_of_setting Fm ha.2.2.2.2.1, VanishingOnXAndXPlus.family_lemma_E_prime_of_source Fm ha.2.2.2.2.2, hb.1, VanishingOnXAndXPlus.family_second_sum_of_source Fm hb.2.1, hb.2.2.1,
    fun Cg cb Cu cT CT C0 A =>
    ⟨hPT Cg cb Cu cT CT C0, hSum Cg cb Cu cT CT C0, hDl Cg cb Cu cT CT C0, hJ90 Cg cb Cu cT CT C0, hJ90p Cg cb Cu cT CT C0, hMOM Cg cb Cu cT CT C0,
      VanishingOnXAndXPlus.family_mass_of_source Fm Cg cb Cu cT CT C0 A (hb.2.2.2 Cg cb Cu cT CT C0 A).1, hSW Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.family_temperature_product_asymptotic_of_bessel_bound Fm Cg cb Cu cT CT C0 (h27 Cg cb Cu cT CT C0) (hE Cg cb Cu cT CT C0),
      hTl Cg cb Cu cT CT C0, hForm Cg cb Cu cT CT C0 A, hSchur Cg cb Cu cT CT C0, hWeylU Cg cb Cu cT CT C0, (hb.2.2.2 Cg cb Cu cT CT C0 A).1, (hb.2.2.2 Cg cb Cu cT CT C0 A).2.1, (hb.2.2.2 Cg cb Cu cT CT C0 A).2.2.1, (hb.2.2.2 Cg cb Cu cT CT C0 A).2.2.2,
      VanishingOnXAndXPlus.family_amplitude_of_source Fm Cg cb Cu cT CT C0 A C1 (hc Cg cb Cu cT CT C0 A), hHH Cg cb Cu cT CT C0 A, hVol Cg cb Cu cT CT C0 A⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hM1, hM2, hMV, hmult, hhad, htr, hmk, fun Cg cb Cu cT CT C0 A => ⟨AuxiliaryNormPrimes.family_mass_third_of_source Fm Cg cb Cu cT CT C0 A (hb1 Cg cb Cu cT CT C0 A), hSW Cg cb Cu cT CT C0 A, hForm Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.family_temperature_product_asymptotic_of_be …`.
-/
theorem AuxiliaryNormPrimes.AdmF_of
    (hb1 : ∀ Cg cb Cu cT CT C0 A, VanishingOnXAndXPlusMass.Conclusion1Family Fm Cg cb Cu cT CT C0 A) (hc1 : ∀ Cg cb Cu cT CT C0, VanishingOnXAndXPlusBranching.ConclusionF1 Fm Cg cb Cu cT CT C0 C1)
    (h27 : ∀ Cg cb Cu cT CT C0, LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT)
    (hPT : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyPlancherelOneParameter Fm Cg cb Cu cT CT C0 C1) (hMOM : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyArchimedeanMomentBound Fm Cg cb Cu cT CT C0 C1)
    (hJ90p : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyDegreeRatioUnitStep Fm Cg cb Cu cT CT C0 C1)
    (hM1 : AuxiliaryNormPrimes.SecondSizeStatement Fm) (hMV : AuxiliaryNormPrimes.FamilyGaugeMassVolumes Fm)
    (hM2 : AuxiliaryNormPrimes.BesselFormLine Fm) (hmult : AuxiliaryNormPrimes.UnitaryBranchingMultiplicityOne) (hhad : AuxiliaryNormPrimes.HadamardDeterminantInequality) (htr : AuxiliaryNormPrimes.BanaszczykTransferenceBound) (hmk : AuxiliaryNormPrimes.MinkowskiFiniteSubgroupOrder)
    (hSW : ∀ Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.LocalGenericDensity Fm Cg cb Cu cT CT C0 A) (hForm : ∀ Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.FamilyFormulaUnderLoopData Fm Cg cb Cu cT CT C0 A)
    (hE : ∀ Cg cb Cu cT CT C0, EpsTF Fm Cg cb Cu cT CT C0) (hTl : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyCriticalTemperatureLower Fm Cg cb Cu cT CT C0)
    (hSum : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyPlancherelFiniteSums Fm Cg cb Cu cT CT C0 C1) (hDl : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyPlancherelDifferenceOperator Fm Cg cb Cu cT CT C0 C1)
    (hJ90 : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyBesselDegreeNormalization Fm Cg cb Cu cT CT C0 C1) (hVol : ∀ Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.FamilyTermVolumeBound Fm C1 X Y Cg cb Cu cT CT C0 A) :
    AuxiliaryNormPrimes.AdmF Fm C1 X Y :=
  ⟨hM1, hM2, hMV, hmult, hhad, htr, hmk, fun Cg cb Cu cT CT C0 A =>
    ⟨AuxiliaryNormPrimes.family_mass_third_of_source Fm Cg cb Cu cT CT C0 A (hb1 Cg cb Cu cT CT C0 A), hSW Cg cb Cu cT CT C0 A, hForm Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.family_temperature_product_asymptotic_of_bessel_bound Fm Cg cb Cu cT CT C0 (h27 Cg cb Cu cT CT C0) (hE Cg cb Cu cT CT C0),
      hTl Cg cb Cu cT CT C0, hPT Cg cb Cu cT CT C0, hSum Cg cb Cu cT CT C0, hDl Cg cb Cu cT CT C0, hJ90 Cg cb Cu cT CT C0, hJ90p Cg cb Cu cT CT C0, hMOM Cg cb Cu cT CT C0, hc1 Cg cb Cu cT CT C0, hVol Cg cb Cu cT CT C0 A⟩⟩

/- English proof (translation)
Take `⟨C, C2, Ch, hC⟩` from `h`. Conclude with `⟨C, Formalism.MainNotions.S.OwnEv.mono (fun _ _ _ _ H => H.1) (hC 0 1 one_pos)⟩`.
-/
theorem VanishingOnXAndXPlusBranching.familyMass_of_massCount (Cg cb Cu cT CT C0 A C1' : ℝ) (h : VanishingOnXAndXPlusBranching.FamilyTargetsAtConstants Fm Cg cb Cu cT CT C0 A C1') : VanishingOnXAndXPlusBranching.ConclusionF1 Fm Cg cb Cu cT CT C0 C1' := by
  obtain ⟨C, C2, Ch, hC⟩ := h
  exact ⟨C, Formalism.MainNotions.S.OwnEv.mono (fun _ _ _ _ H => H.1) (hC 0 1 one_pos)⟩

/- English proof (translation)
Establish `ha : VanishingOnXAndXPlusGlobal.ConclusionOnFamily Fm` using `Sa (VanishingOnXAndXPlusGlobal.AdmF_of Fm hGlue hhad hKron)`. Establish `h48 : VanishingOnXAndXPlusGluing.OrbitValuationBound Fm` using `S48 (VanishingOnXAndXPlusGluing.AdmF_of Fm hGlue hhad hKron)`. Establish `hc : ∀ C1', VanishingOnXAndXPlusBranching.OrbitValuationBound Fm C1'` using `fun C1' => Sc C1' (VanishingOnXAndXPlusBranching.AdmF_of Fm C1' (fun Cg cb Cu cT CT C0 => hPT Cg cb Cu cT CT C0 C1') (fun Cg cb Cu cT CT C0 => hMOM Cg cb Cu cT CT C0 C1') (fun Cg cb Cu cT CT C0 => hJ90p Cg cb Cu cT CT C0 C1') hmult hhad hWeyl (fun Cg cb Cu cT CT C0 => hDl Cg cb C …`. Establish `hc1 : ∀ Cg cb Cu cT CT C0 C1', VanishingOnXAndXPlusBranching.ConclusionF1 Fm Cg cb Cu cT CT C0 C1'` using `fun Cg cb Cu cT CT C0 C1' => VanishingOnXAndXPlusBranching.familyMass_of_massCount Fm Cg cb Cu cT CT C0 0 C1' (hc C1' Cg cb Cu cT CT C0 0)`. Establish `hb : VanishingOnXAndXPlusMass.ConclusionOnFamily Fm` using `Sb (VanishingOnXAndXPlusMass.AdmF_of Fm ha.2.1 ha.2.2.2.1 hc1 h27 hPT hMOM hJ90p hM1 hMV hM2 hmult hhad htr hmk hSW hForm hE hTl hSum hDl hJ90)`.

Establish `hd : VanishingOnXAndXPlus.OrbitValuationBound Fm c` using `Sd (VanishingOnXAndXPlus.AdmF_of Fm C1 X Y ha hb (hc C1) h27 (fun Cg cb Cu cT CT C0 => hPT Cg cb Cu cT CT C0 C1) (fun Cg cb Cu cT CT C0 => hMOM Cg cb Cu cT CT C0 C1) (fun Cg cb Cu cT CT C0 => hJ90p Cg cb Cu cT CT C0 C1) hM1 hMV hM2 hmult hhad htr hmk hSW hForm hE hTl (fun Cg cb C …`. Establish `h28 : AuxiliaryNormPrimes.OrbitValuationBound Fm c` using `S28 (AuxiliaryNormPrimes.AdmF_of Fm C1 X Y (fun Cg cb Cu cT CT C0 A => (hb.2.2.2 Cg cb Cu cT CT C0 A).1) (fun Cg cb Cu cT CT C0 => hc1 Cg cb Cu cT CT C0 C1) h27 (fun Cg cb Cu cT CT C0 => hPT Cg cb Cu cT CT C0 C1) (fun Cg cb Cu cT CT C0 => hMOM Cg cb Cu cT CT C0 C1) (fun Cg cb Cu …`. Conclude with `⟨ha, h48, hc, hb, hd, h28⟩`.
-/
theorem S5.family_statements_all (c : ℝ)
    (Sa : VanishingOnXAndXPlusGlobal.KudlaFamilyStatement Fm) (S48 : VanishingOnXAndXPlusGluing.KudlaFamilyStatement Fm) (Sc : ∀ C1', VanishingOnXAndXPlusBranching.KudlaFamilyStatement Fm C1') (Sb : VanishingOnXAndXPlusMass.KudlaFamilyStatement Fm)
    (Sd : VanishingOnXAndXPlus.KudlaFamilyStatement Fm C1 X Y c) (S28 : AuxiliaryNormPrimes.KudlaFamilyStatement Fm C1 X Y c)
    (h27 : ∀ Cg cb Cu cT CT C0, LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT)
    (hPT : ∀ Cg cb Cu cT CT C0 C1', AuxiliaryNormPrimes.FamilyPlancherelOneParameter Fm Cg cb Cu cT CT C0 C1') (hMOM : ∀ Cg cb Cu cT CT C0 C1', AuxiliaryNormPrimes.FamilyArchimedeanMomentBound Fm Cg cb Cu cT CT C0 C1')
    (hJ90p : ∀ Cg cb Cu cT CT C0 C1', AuxiliaryNormPrimes.FamilyDegreeRatioUnitStep Fm Cg cb Cu cT CT C0 C1')
    (hM1 : AuxiliaryNormPrimes.SecondSizeStatement Fm) (hMV : AuxiliaryNormPrimes.FamilyGaugeMassVolumes Fm)
    (hM2 : AuxiliaryNormPrimes.BesselFormLine Fm) (hmult : AuxiliaryNormPrimes.UnitaryBranchingMultiplicityOne) (hhad : AuxiliaryNormPrimes.HadamardDeterminantInequality) (htr : AuxiliaryNormPrimes.BanaszczykTransferenceBound) (hmk : AuxiliaryNormPrimes.MinkowskiFiniteSubgroupOrder)
    (hWeyl : VanishingOnXAndXPlusBranching.FamilyTwelfthHypothesis Fm) (hGlue : VanishingOnXAndXPlusGlobal.admF1 Fm) (hKron : VanishingOnXAndXPlusGlobal.admF3 Fm)
    (hSW : ∀ Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.LocalGenericDensity Fm Cg cb Cu cT CT C0 A) (hForm : ∀ Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.FamilyFormulaUnderLoopData Fm Cg cb Cu cT CT C0 A)
    (hE : ∀ Cg cb Cu cT CT C0, EpsTF Fm Cg cb Cu cT CT C0) (hTl : ∀ Cg cb Cu cT CT C0, AuxiliaryNormPrimes.FamilyCriticalTemperatureLower Fm Cg cb Cu cT CT C0)
    (hSum : ∀ Cg cb Cu cT CT C0 C1', AuxiliaryNormPrimes.FamilyPlancherelFiniteSums Fm Cg cb Cu cT CT C0 C1') (hDl : ∀ Cg cb Cu cT CT C0 C1', AuxiliaryNormPrimes.FamilyPlancherelDifferenceOperator Fm Cg cb Cu cT CT C0 C1')
    (hJ90 : ∀ Cg cb Cu cT CT C0 C1', AuxiliaryNormPrimes.FamilyBesselDegreeNormalization Fm Cg cb Cu cT CT C0 C1') (hSchur : ∀ Cg cb Cu cT CT C0 C1', VanishingOnXAndXPlusBranching.FamilyWeylAndVandermonde Fm Cg cb Cu cT CT C0 C1')
    (hHH : ∀ Cg cb Cu cT CT C0 A, VanishingOnXAndXPlus.FamilyTermMassEstimate Fm Cg cb Cu cT CT C0 A) (hVol : ∀ Cg cb Cu cT CT C0 A, AuxiliaryNormPrimes.FamilyTermVolumeBound Fm C1 X Y Cg cb Cu cT CT C0 A)
    (hWeylU : ∀ Cg cb Cu cT CT C0, VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0) :
    VanishingOnXAndXPlusGlobal.ConclusionOnFamily Fm ∧ VanishingOnXAndXPlusGluing.OrbitValuationBound Fm ∧ (∀ C1', VanishingOnXAndXPlusBranching.OrbitValuationBound Fm C1') ∧ VanishingOnXAndXPlusMass.ConclusionOnFamily Fm ∧ VanishingOnXAndXPlus.OrbitValuationBound Fm c ∧ AuxiliaryNormPrimes.OrbitValuationBound Fm c := by
  have ha : VanishingOnXAndXPlusGlobal.ConclusionOnFamily Fm := Sa (VanishingOnXAndXPlusGlobal.AdmF_of Fm hGlue hhad hKron)
  have h48 : VanishingOnXAndXPlusGluing.OrbitValuationBound Fm := S48 (VanishingOnXAndXPlusGluing.AdmF_of Fm hGlue hhad hKron)
  have hc : ∀ C1', VanishingOnXAndXPlusBranching.OrbitValuationBound Fm C1' := fun C1' => Sc C1' (VanishingOnXAndXPlusBranching.AdmF_of Fm C1' (fun Cg cb Cu cT CT C0 => hPT Cg cb Cu cT CT C0 C1')
    (fun Cg cb Cu cT CT C0 => hMOM Cg cb Cu cT CT C0 C1') (fun Cg cb Cu cT CT C0 => hJ90p Cg cb Cu cT CT C0 C1') hmult hhad hWeyl (fun Cg cb Cu cT CT C0 => hDl Cg cb Cu cT CT C0 C1') hTl
    (fun Cg cb Cu cT CT C0 => hJ90 Cg cb Cu cT CT C0 C1') (fun Cg cb Cu cT CT C0 => hSchur Cg cb Cu cT CT C0 C1'))
  have hc1 : ∀ Cg cb Cu cT CT C0 C1', VanishingOnXAndXPlusBranching.ConclusionF1 Fm Cg cb Cu cT CT C0 C1' := fun Cg cb Cu cT CT C0 C1' =>
    VanishingOnXAndXPlusBranching.familyMass_of_massCount Fm Cg cb Cu cT CT C0 0 C1' (hc C1' Cg cb Cu cT CT C0 0)
  have hb : VanishingOnXAndXPlusMass.ConclusionOnFamily Fm := Sb (VanishingOnXAndXPlusMass.AdmF_of Fm ha.2.1 ha.2.2.2.1 hc1 h27 hPT hMOM hJ90p hM1 hMV hM2 hmult hhad htr hmk
    hSW hForm hE hTl hSum hDl hJ90)
  have hd : VanishingOnXAndXPlus.OrbitValuationBound Fm c := Sd (VanishingOnXAndXPlus.AdmF_of Fm C1 X Y ha hb (hc C1) h27 (fun Cg cb Cu cT CT C0 => hPT Cg cb Cu cT CT C0 C1)
    (fun Cg cb Cu cT CT C0 => hMOM Cg cb Cu cT CT C0 C1) (fun Cg cb Cu cT CT C0 => hJ90p Cg cb Cu cT CT C0 C1) hM1 hMV hM2 hmult hhad htr hmk hSW hForm hE hTl
    (fun Cg cb Cu cT CT C0 => hSum Cg cb Cu cT CT C0 C1) (fun Cg cb Cu cT CT C0 => hDl Cg cb Cu cT CT C0 C1) (fun Cg cb Cu cT CT C0 => hJ90 Cg cb Cu cT CT C0 C1) hHH hVol hWeyl
    (fun Cg cb Cu cT CT C0 => hSchur Cg cb Cu cT CT C0 C1) hWeylU)
  have h28 : AuxiliaryNormPrimes.OrbitValuationBound Fm c := S28 (AuxiliaryNormPrimes.AdmF_of Fm C1 X Y (fun Cg cb Cu cT CT C0 A => (hb.2.2.2 Cg cb Cu cT CT C0 A).1) (fun Cg cb Cu cT CT C0 => hc1 Cg cb Cu cT CT C0 C1) h27
    (fun Cg cb Cu cT CT C0 => hPT Cg cb Cu cT CT C0 C1) (fun Cg cb Cu cT CT C0 => hMOM Cg cb Cu cT CT C0 C1) (fun Cg cb Cu cT CT C0 => hJ90p Cg cb Cu cT CT C0 C1) hM1 hMV hM2 hmult hhad htr hmk
    hSW hForm hE hTl (fun Cg cb Cu cT CT C0 => hSum Cg cb Cu cT CT C0 C1) (fun Cg cb Cu cT CT C0 => hDl Cg cb Cu cT CT C0 C1) (fun Cg cb Cu cT CT C0 => hJ90 Cg cb Cu cT CT C0 C1) hVol)
  exact ⟨ha, h48, hc, hb, hd, h28⟩

end Assembly

end Formalism.MainNotions

end
