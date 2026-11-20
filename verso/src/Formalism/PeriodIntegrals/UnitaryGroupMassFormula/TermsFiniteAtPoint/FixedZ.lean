import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.FixedRel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ZhatIntegralHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.SkewSolve
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ResFin
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitRow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdentityCellTrace.TraceOneHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.PositiveWeightHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ResFinAlt

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Saturated

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Take `⟨y, hy, h⟩` from `exists_integral_multiples ℤ ℚ (L := E) s`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hi : IsIntegral ℤ ((y : E) * x)` using `by simpa [zsmul_eq_mul] using h x hx`. Establish `hn : ((y.natAbs : ℕ) : E) = (((y.natAbs : ℕ) : ℤ) : E)` using `(Int.cast_natCast _).symm`. Break down `Int.natAbs_eq y with h' | h'` into its components or cases.

Use `⟨⟨_, hi⟩, ?_⟩ show (y : E) * x = _` and prove the remaining obligations. Rewrite using `[hn, ← h']`. Use `⟨-⟨_, hi⟩, ?_⟩ show -((y : E) * x) = _` and prove the remaining obligations. Establish `h2 : ((y.natAbs : ℕ) : ℤ) = -y` using `by omega`. Rewrite using `[hn, h2]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem common_den (s : Finset E) : ∃ n : ℕ, 0 < n ∧ ∀ x ∈ s, IntE ((n : E) * x) := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := E) s
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun x hx => ?_⟩
  have hi : IsIntegral ℤ ((y : E) * x) := by simpa [zsmul_eq_mul] using h x hx
  have hn : ((y.natAbs : ℕ) : E) = (((y.natAbs : ℕ) : ℤ) : E) := (Int.cast_natCast _).symm
  rcases Int.natAbs_eq y with h' | h'
  · refine ⟨⟨_, hi⟩, ?_⟩
    show (y : E) * x = _
    rw [hn, ← h']
  · refine ⟨-⟨_, hi⟩, ?_⟩
    show -((y : E) * x) = _
    have h2 : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [hn, h2]
    push_cast
    ring

/- English proof (translation)
Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b`. Simplify `F.fl.z_norm` using `[frame, FlagG.fvec]`. Establish `h` using `F.fl.z_orth j`. Establish `: S.hT F.fl.z (F.fl.e j) = 0` using `by rw [← herm_star, h]; simp`. Simplify `this` using `[frame, FlagG.fvec, Fin.castSucc_ne_last]`.

Simplify `F.fl.z_orth i` using `[frame, FlagG.fvec, Fin.castSucc_ne_last]`. Simplify `F.fl.e_iso i j` using `[frame, FlagG.fvec, Fin.castSucc_ne_last]`.
-/
theorem gram_frame {T' : E} (F : LFlag S r T') (a b : Fin (r + 1)) :
    S.hT (frame F a) (frame F b) = if a = Fin.last r ∧ b = Fin.last r then -T' else 0 := by
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simpa [frame, FlagG.fvec] using F.fl.z_norm
  · have h := F.fl.z_orth j
    have : S.hT F.fl.z (F.fl.e j) = 0 := by rw [← herm_star, h]; simp
    simpa [frame, FlagG.fvec, Fin.castSucc_ne_last] using this
  · simpa [frame, FlagG.fvec, Fin.castSucc_ne_last] using F.fl.z_orth i
  · simpa [frame, FlagG.fvec, Fin.castSucc_ne_last] using F.fl.e_iso i j

/- English proof (translation)
Establish `hle : Xplus F ≤ LinearMap.ker (S.hT.flip x)`. Use `sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Simplify using `[he a]`. Introduce `w hw`.

Rewrite `hw` using `[Set.mem_singleton_iff]`. Substitute `hw` using the available equality. Simplify using `[hz]`. Simplify using `only [orth, Submodule.mem_iInf]`. Introduce `w hw`.

Use `hle hw` as an intermediate fact. Simplify using `using this`.
-/
theorem mem_orth_Xplus {T : E} (F : LFlag S r T) (x : S.V) (he : ∀ a, S.hT (F.fl.e a) x = 0)
    (hz : S.hT F.fl.z x = 0) : x ∈ orth S (Xplus F) := by
  have hle : Xplus F ≤ LinearMap.ker (S.hT.flip x) := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨a, rfl⟩
      simp [he a]
    · intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      simp [hz]
  simp only [orth, Submodule.mem_iInf]
  intro w hw
  have := hle hw
  simpa using this

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Simplify using `[ZhatL, Zhat, brS, frame, FlagG.fvec, lf]`.
-/
theorem zhat_cs (D : D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (c : Fin D.R.rS) (b : Fin (D.R.rS + 1)) :
    ZhatL (lf D F0) F' (Fin.castSucc c) b = (VS D).hT (F0.e c) (frame F' b) := by
  simp [ZhatL, Zhat, brS, frame, FlagG.fvec, lf]

/- English proof (translation)
Simplify using `[ZhatL, Zhat, brS, frame, FlagG.fvec, lf]`.
-/
theorem zhat_last (D : D7) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (b : Fin (D.R.rS + 1)) :
    ZhatL (lf D F0) F' (Fin.last D.R.rS) b = (VS D).hT F0.z (frame F' b) := by
  simp [ZhatL, Zhat, brS, frame, FlagG.fvec, lf]

/- English proof (translation)
Introduce `D u u' _hsig F0 Λ hΛ Z`. Use `set Y := {y : Carrier (PD D Λ (lf D F0) u') | Gval (lf D F0) y.1 ≠ 0 ∧ ZhatL (lf D F0) y.1 = Z} with hY`. Break down `Set.eq_empty_or_nonempty Y with hE | ⟨y0, hy0⟩` into its components or cases. Rewrite using `[hE, Set.image_empty]`. Conclude with `Set.finite_empty`.

Take `⟨f, L, hff, hef, hLp, hzL, hΛeq⟩` from `split_row_iso D u F0 Λ hΛ`. Take `⟨hnd, hfint⟩` from `hFI D F0 Λ f L hff hef hLp hΛeq`. Take `⟨θ, hθ⟩` from `PI.UnitaryGroupMassFormula.IdCellInSW.traceOne_holds D`. Take `⟨_, ⟨hlat, hU, hlift0, _⟩, hX0⟩` from `hΛ`. Establish `hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 D.host.E, (o : D.host.E) = (VS D).hT x y` using `fun x hx y hy => hT_int D Λ hU hx hy`.

Establish `he : ∀ c, F0.e c ∈ Λ` using `e_mem_of_XS D Λ (lf D F0) hX0`. Establish `hz0 : F0.z ∈ Λ` using `hlift0.1`. Set `β : Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E` to `fun c b => Z (Fin.castSucc c) b`. Establish `hind : ∀ w : Fin D.R.rS → D.host.E, (∀ b, ∑ c, w c * β c b = 0) → w = 0`. Introduce `w hw`.

Assume the negation of the conclusion as `hne`. Take `⟨h1, h2⟩` from `hRD D.host.E D.R.rS Z w hne hw`. Apply `hy0.1` to reduce the goal to its premises. Establish `hZ : Zhat F0 y0.1.fl = Z` using `hy0.2`. Simplify using `only [Gval, Gflag, Dl, lf, hZ, h1, h2]`.

Simplify using the standard rewrite rules. Take `⟨Q, v, l, hβQ, hv, hQβ⟩` from `hRI D.host.E D.R.rS β hind`. Take `⟨nQ, hnQ, hQint⟩` from `common_den (Finset.univ.image (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => Q p.1 p.2))`. Take `⟨nv, hnv, hvint⟩` from `common_den (Finset.univ.image v)`. Establish `hQint' : ∀ b c, IntE ((nQ : D.host.E) * Q b c)` using `fun b c => hQint _ (Finset.mem_image.2 ⟨(b, c), Finset.mem_univ _, rfl⟩)`.

Establish `hvint' : ∀ b, IntE ((nv : D.host.E) * v b)` using `fun b => hvint _ (Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩)`. Take `⟨R, hRfin, ρ, hρ⟩` from `hRF D.host.E (VS D).V Λ hlat.fg ((ndS D * nQ) ^ 2) (by positivity)`. Use `set nd := ndS D with hnd_def`. Establish `hfe : ∀ a b, (VS D).hT (f a) (F0.e b) = if a = b then 1 else 0` using `fun a b => by`. Rewrite using `[← herm_star, hef b a]`.

Distinguish the cases in `h : b = a`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Establish `hze : ∀ c, (VS D).hT F0.z (F0.e c) = 0` using `fun c => by rw [← herm_star, F0.z_orth c]; simp`.

Establish `hfz : ∀ c, (VS D).hT (f c) F0.z = 0` using `fun c => (hLp F0.z hzL c).2`. Establish `hmemE : ∀ (x : D.host.E) (w : (VS D).V), IntE x → w ∈ Λ → x • w ∈ Λ`. Introduce and unpack `x w ⟨o, rfl⟩ hw`. Use `show (algebraMap (𝓞 D.host.E) D.host.E o) • w ∈ Λ`. Rewrite using `[algebraMap_smul]`.

Conclude with `Λ.smul_mem o hw`. Establish `hnat : ∀ (k : ℕ) (w : (VS D).V), w ∈ Λ → (k : D.host.E) • w ∈ Λ` using `fun k w hw => hmemE _ w (IntE.nat k) hw`. Establish `hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0`. Use `(D.mem u).A.T_prime.pos` as an intermediate fact. Conclude with `this.ne'` after adjusting the coercions.

Set `yv : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) → (VS D).V` to `fun y => ∑ b, v b • frame y b`. Set `ι2 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) → (VS D).V` to `fun y => ((nd * nv : ℕ) : D.host.E) • piL F0.e f (yv y)`. Set `hz : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) → D.host.E` to `fun y => (VS D).hT F0.z (ι2 y)`. Set `xf : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) → (VS D).V` to `fun y => ((Tu D u : ℕ) : D.host.E) • ι2 y + hz y • F0.z`. Establish `hβy : ∀ y ∈ Y, ∀ c b, (VS D).hT (F0.e c) (frame y.1 b) = β c b`.

Introduce `y hy c b`. Rewrite using `[← zhat_cs D F0 y.1 c b, hy.2]`. Establish `hzy : ∀ y ∈ Y, ∀ b, (VS D).hT F0.z (frame y.1 b) = Z (Fin.last D.R.rS) b`. Introduce `y hy b`. Rewrite using `[← zhat_last D F0 y.1 b, hy.2]`.

Establish `hyΛ : ∀ y : Carrier (PD D Λ (lf D F0) u'), ∀ b, frame y.1 b ∈ Λ`. Introduce `y b`. Take `⟨hlift, _, _, hX⟩` from `y.2`. Conclude with `frame_mem D Λ y.1 hX hlift.1 b`. Establish `hyve : ∀ y ∈ Y, ∀ c, (VS D).hT (F0.e c) (yv y.1) = 0`.

Introduce `y hy c`. Simplify using `only [yv, map_sum, map_smul, smul_eq_mul, hβy y hy]`. Rewrite using `[← hv c]`. Conclude with `Finset.sum_congr rfl fun b _ => mul_comm _ _`. Establish `hpie : ∀ c x, (VS D).hT (F0.e c) (piL F0.e f x) = (VS D).hT (F0.e c) x` using `fun c x => by`.

Simplify using `[piL_apply, map_sub, map_sum, F0.e_iso]`. Establish `hpif : ∀ c x, (VS D).hT (f c) (piL F0.e f x) = 0` using `fun c x => by`. Simplify using `[piL_apply, map_sub, map_sum, hfe]`. Establish `hpiz : ∀ x, (VS D).hT F0.z (piL F0.e f x) = (VS D).hT F0.z x` using `fun x => by`. Simplify using `[piL_apply, map_sub, map_sum, hze]`.

Establish `hι2 : ∀ y : Carrier (PD D Λ (lf D F0) u'), ι2 y.1 ∈ Λ`. Introduce `y`. Set `lam : (VS D).V` to `∑ b, ((nv : D.host.E) * v b) • frame y.1 b`. Establish `hlam : lam ∈ Λ` using `Λ.sum_mem fun b _ => hmemE _ _ (hvint' b) (hyΛ y b)`. Establish `: ι2 y.1 = (nd : D.host.E) • lam - ∑ c, ((nd : D.host.E) * (VS D).hT (f c) lam) • F0.e c`.

Establish `h1 : (nv : D.host.E) • yv y.1 = lam`. Simplify using `only [yv, lam, Finset.smul_sum, smul_smul]`. Establish `h2 : ι2 y.1 = (nd : D.host.E) • piL F0.e f lam`. Simplify using `only [ι2]`. Rewrite using `[← h1, map_smul, smul_smul]`.

Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[h2, piL_apply, smul_sub]`. Use `congr 1`. Rewrite using `[Finset.smul_sum]`.

Simplify using `only [smul_smul]`. Rewrite using `[this]`. Conclude with `Λ.sub_mem (hnat nd _ hlam) (Λ.sum_mem fun c _ => hmemE _ _ (hfint _ hlam c) (he c))`. Establish `hhz : ∀ y ∈ Y, hz y.1 = ((nd * nv : ℕ) : D.host.E) * ∑ b, v b * Z (Fin.last D.R.rS) b`. Introduce `y hy`.

Simplify using `only [hz, ι2, map_smul, smul_eq_mul, hpiz, yv, map_sum, hzy y hy]`. Establish `hyvn : ∀ y : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), (VS D).hT (yv y) (yv y) = (VS D).hT (yv y0.1) (yv y0.1)`. Introduce `y`. Simplify using `only [yv, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, gram_frame]`. Establish `hpin : ∀ y ∈ Y, (VS D).hT (piL F0.e f (yv y.1)) (piL F0.e f (yv y.1)) = (VS D).hT (yv y.1) (yv y.1)`.

Introduce `y hy`. Establish `h1 : ∀ c, (VS D).hT (yv y.1) (F0.e c) = 0` using `fun c => by rw [← herm_star, hyve y hy c]; simp`. Simplify using `[piL_apply, map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.map_smulₛₗ, hyve y hy, h1, F0.e_iso]`. Use `set hzc : D.host.E := ((nd * nv : ℕ) : D.host.E) * ∑ b, v b * Z (Fin.last D.R.rS) b with hzc_def`. Use `set K : D.host.E := ((Tu D u : ℕ) : D.host.E) ^ 2 * ((((nd * nv : ℕ) : D.host.E)) ^ 2 * (VS D).hT (yv y0.1) (yv y0.1)) + ((Tu D u : ℕ) : D.host.E) * hzc * star hzc with hK_def`.

Establish `hxK : ∀ y ∈ Y, (VS D).hT (xf y.1) (xf y.1) = K`. Introduce `y hy`. Establish `hιz : (VS D).hT (ι2 y.1) F0.z = star (hz y.1)` using `by rw [← herm_star]`. Establish `hιι : (VS D).hT (ι2 y.1) (ι2 y.1) = (((nd * nv : ℕ) : D.host.E)) ^ 2 * (VS D).hT (yv y0.1) (yv y0.1)`. Simplify using `only [ι2, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, star_natCast, hpin y hy, hyvn]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hzz : (VS D).hT F0.z F0.z = -((Tu D u : ℕ) : D.host.E)` using `F0.z_norm`. Simplify using `only [xf, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, star_natCast, hιz, hιι, hzz]`. Establish `hh : hz y.1 = hzc` using `hhz y hy`. Rewrite using `[show (VS D).hT F0.z (ι2 y.1) = hz y.1 from rfl, hh]`.

Simplify using `only [hK_def]`. Expand and normalize the polynomial expressions, which then agree. Set `P : Submodule D.host.E (VS D).V` to `orth (VS D) (Xplus (lf D F0)) ⊓ ⨅ c, LinearMap.ker ((VS D).hT (f c))`. Establish `hpos : ∀ x ∈ P, x ≠ 0 → ∀ τ : D.host.E →+* ℂ, 0 < (τ ((VS D).hT x x)).re`. Introduce `x hx hne τ`.

Take `⟨hxo, hxf⟩` from `Submodule.mem_inf.1 hx`. Use `PI.UnitaryGroupMassFormula.BetaModX.positive_weight_holds D (Tu D u) (lf D F0) τ x (D.mem u).A.T_prime.pos hxo ?_` and prove the remaining obligations. Introduce `hxX`. Take `⟨t, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun D.host.E).1 hxX`. Apply `hne` to reduce the goal to its premises.

Establish `ht : ∀ c, t c = 0`. Introduce `c`. Use `LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hxf c)` as an intermediate fact. Simplify `this` using `[map_sum, hfe]`. Simplify using `[ht]`.

Establish `hxP : ∀ y ∈ Y, xf y.1 ∈ P`. Introduce `y hy`. Use `Submodule.mem_inf.2 ⟨mem_orth_Xplus (lf D F0) _ (fun a => ?_) ?_, (Submodule.mem_iInf _).2 fun c => ?_⟩` and prove the remaining obligations. Use `show (VS D).hT (F0.e a) (xf y.1) = 0`. Simplify using `[xf, ι2, map_add, map_smul, hpie, hyve y hy, F0.z_orth]`.

Use `show (VS D).hT F0.z (xf y.1) = 0`. Simplify using `only [xf, map_add, map_smul, smul_eq_mul, F0.z_norm]`. Express the relevant statement in the definitionally equal form `((Tu D u : ℕ) : D.host.E) * hz y.1 + hz y.1 * -((Tu D u : ℕ) : D.host.E) = 0`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[LinearMap.mem_ker]`.

Simplify using `[xf, ι2, map_add, map_smul, hpif, hfz]`. Establish `hxΛ : ∀ y : Carrier (PD D Λ (lf D F0) u'), xf y.1 ∈ Λ` using `fun y => Λ.add_mem (hnat _ _ (hι2 y)) (hmemE _ _ (hint _ hz0 _ (hι2 y)) hz0)`. Use `haveI := hRfin`. Set `κ : Carrier (PD D Λ (lf D F0) u') → (VS D).V × (Fin (D.R.rS + 1) → R)` to `fun y => (xf y.1, fun b => ρ (frame y.1 b))`. Establish `hfinX` using `hS D.host.E (VS D) Λ hlat P hpos K`.

Establish `hκ : κ '' Y ⊆ {x | x ∈ Λ ∧ x ∈ P ∧ (VS D).hT x x = K} ×ˢ Set.univ`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `⟨⟨hxΛ y, hxP y hy, hxK y hy⟩, trivial⟩`. Establish `hκfin : (κ '' Y).Finite` using `(hfinX.prod Set.finite_univ).subset hκ`. Establish `hzt : ∀ y : Carrier (PD D Λ (lf D F0) u'), y.1.zt = frame y.1 (Fin.last D.R.rS)`.

Introduce `y`. Rewrite using `[y.2.1.2]`. Simplify using `[frame, FlagG.fvec]`. Establish `hrel : ∀ y1 ∈ Y, ∀ y2 ∈ Y, κ y1 = κ y2 → mk Λ (lf D F0) (PD D Λ (lf D F0) u') y1 = mk Λ (lf D F0) (PD D Λ (lf D F0) u') y2`. Introduce `y1 hy1 y2 hy2 hκ12`.

Establish `hx : xf y1.1 = xf y2.1` using `congrArg Prod.fst hκ12`. Establish `hr : ∀ b, ρ (frame y1.1 b) = ρ (frame y2.1 b)` using `fun b => congrFun (congrArg Prod.snd hκ12) b`. Establish `hδ : ∀ b, ∃ lam ∈ Λ, frame y2.1 b - frame y1.1 b = (((nd * nQ) ^ 2 : ℕ) : D.host.E) • lam` using `fun b => hρ _ (hyΛ y1 b) _ (hyΛ y2 b) (hr b)`. Establish `hι : piL F0.e f (∑ b, v b • frame y1.1 b) = piL F0.e f (∑ b, v b • frame y2.1 b)`. Establish `h1 : ((Tu D u : ℕ) : D.host.E) • ι2 y1.1 = ((Tu D u : ℕ) : D.host.E) • ι2 y2.1`.

Use `hx` as an intermediate fact. Simplify using `only [xf] at this`. Rewrite `this` using `[show hz y1.1 = hzc from hhz y1 hy1, show hz y2.1 = hzc from hhz y2 hy2]`. Conclude with `add_right_cancel this`. Establish `h2` using `smul_right_injective (VS D).V hT0 h1`.

Establish `hne : ((nd * nv : ℕ) : D.host.E) ≠ 0`. Establish `: 0 < nd * nv` using `Nat.mul_pos hnd hnv`. Conclude with `this.ne'` after adjusting the coercions. Conclude with `smul_right_injective (VS D).V hne h2`. Conclude with `Quot.sound (related_gen hH hSk Λ (lf D F0) f hint he hef θ hθ nd nQ hfint β Q v l hind hβQ hv hQβ hQint' y1.1 y2.1 (hzt y1) (hzt y2) (hyΛ y1) (hβy y1 hy1) (hβy y2 hy2) (fun a b => by rw [gram_frame, gram_frame]) hδ hι)`.

Set `g : (VS D).V × (Fin (D.R.rS + 1) → R) → TermQ Λ (lf D F0) (PD D Λ (lf D F0) u')` to `fun t => if h : ∃ y ∈ Y, κ y = t then mk Λ (lf D F0) (PD D Λ (lf D F0) u') (Classical.choose h) else mk Λ (lf D F0) (PD D Λ (lf D F0) u') y0`. Use `(hκfin.image g).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `⟨κ y, ⟨y, hy, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `h : ∃ y' ∈ Y, κ y' = κ y` using `⟨y, hy, rfl⟩`.

Simplify using `only [g, dif_pos h]`. Take `⟨hy', hκ'⟩` from `Classical.choose_spec h`. Conclude with `hrel _ hy' _ hy hκ'`.
-/
theorem fixedZhat_of (hH : HeisOp) (hSk : SkewSolve) (hS : ShortFin) (hRD : RowsDep) (hRI : RightInv)
    (hFI : FInt) (hRF : ResFin) : FixedZhatFinite := by
  intro D u u' _hsig F0 Λ hΛ Z
  set Y := {y : Carrier (PD D Λ (lf D F0) u') | Gval (lf D F0) y.1 ≠ 0 ∧ ZhatL (lf D F0) y.1 = Z} with hY
  rcases Set.eq_empty_or_nonempty Y with hE | ⟨y0, hy0⟩
  · rw [hE, Set.image_empty]
    exact Set.finite_empty
  obtain ⟨f, L, hff, hef, hLp, hzL, hΛeq⟩ := split_row_iso D u F0 Λ hΛ
  obtain ⟨hnd, hfint⟩ := hFI D F0 Λ f L hff hef hLp hΛeq
  obtain ⟨θ, hθ⟩ := PI.UnitaryGroupMassFormula.IdCellInSW.traceOne_holds D
  obtain ⟨_, ⟨hlat, hU, hlift0, _⟩, hX0⟩ := hΛ
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ o : 𝓞 D.host.E, (o : D.host.E) = (VS D).hT x y :=
    fun x hx y hy => hT_int D Λ hU hx hy
  have he : ∀ c, F0.e c ∈ Λ := e_mem_of_XS D Λ (lf D F0) hX0
  have hz0 : F0.z ∈ Λ := hlift0.1
  let β : Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E := fun c b => Z (Fin.castSucc c) b
  have hind : ∀ w : Fin D.R.rS → D.host.E, (∀ b, ∑ c, w c * β c b = 0) → w = 0 := by
    intro w hw
    by_contra hne
    obtain ⟨h1, h2⟩ := hRD D.host.E D.R.rS Z w hne hw
    apply hy0.1
    have hZ : Zhat F0 y0.1.fl = Z := hy0.2
    simp only [Gval, Gflag, Dl, lf, hZ, h1, h2]
    simp
  obtain ⟨Q, v, l, hβQ, hv, hQβ⟩ := hRI D.host.E D.R.rS β hind
  obtain ⟨nQ, hnQ, hQint⟩ := common_den (Finset.univ.image (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => Q p.1 p.2))
  obtain ⟨nv, hnv, hvint⟩ := common_den (Finset.univ.image v)
  have hQint' : ∀ b c, IntE ((nQ : D.host.E) * Q b c) := fun b c =>
    hQint _ (Finset.mem_image.2 ⟨(b, c), Finset.mem_univ _, rfl⟩)
  have hvint' : ∀ b, IntE ((nv : D.host.E) * v b) := fun b => hvint _ (Finset.mem_image.2 ⟨b, Finset.mem_univ _, rfl⟩)
  obtain ⟨R, hRfin, ρ, hρ⟩ := hRF D.host.E (VS D).V Λ hlat.fg ((ndS D * nQ) ^ 2) (by positivity)
  set nd := ndS D with hnd_def
  have hfe : ∀ a b, (VS D).hT (f a) (F0.e b) = if a = b then 1 else 0 := fun a b => by
    rw [← herm_star, hef b a]
    by_cases h : b = a
    · subst h; simp
    · simp [h, Ne.symm h]
  have hze : ∀ c, (VS D).hT F0.z (F0.e c) = 0 := fun c => by rw [← herm_star, F0.z_orth c]; simp
  have hfz : ∀ c, (VS D).hT (f c) F0.z = 0 := fun c => (hLp F0.z hzL c).2
  have hmemE : ∀ (x : D.host.E) (w : (VS D).V), IntE x → w ∈ Λ → x • w ∈ Λ := by
    rintro x w ⟨o, rfl⟩ hw
    show (algebraMap (𝓞 D.host.E) D.host.E o) • w ∈ Λ
    rw [algebraMap_smul]
    exact Λ.smul_mem o hw
  have hnat : ∀ (k : ℕ) (w : (VS D).V), w ∈ Λ → (k : D.host.E) • w ∈ Λ :=
    fun k w hw => hmemE _ w (IntE.nat k) hw
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by
    have := (D.mem u).A.T_prime.pos
    exact_mod_cast this.ne'

  let yv : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) → (VS D).V := fun y => ∑ b, v b • frame y b
  let ι2 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) → (VS D).V :=
    fun y => ((nd * nv : ℕ) : D.host.E) • piL F0.e f (yv y)
  let hz : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) → D.host.E := fun y => (VS D).hT F0.z (ι2 y)
  let xf : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) → (VS D).V :=
    fun y => ((Tu D u : ℕ) : D.host.E) • ι2 y + hz y • F0.z

  have hβy : ∀ y ∈ Y, ∀ c b, (VS D).hT (F0.e c) (frame y.1 b) = β c b := by
    intro y hy c b
    rw [← zhat_cs D F0 y.1 c b, hy.2]
  have hzy : ∀ y ∈ Y, ∀ b, (VS D).hT F0.z (frame y.1 b) = Z (Fin.last D.R.rS) b := by
    intro y hy b
    rw [← zhat_last D F0 y.1 b, hy.2]
  have hyΛ : ∀ y : Carrier (PD D Λ (lf D F0) u'), ∀ b, frame y.1 b ∈ Λ := by
    intro y b
    obtain ⟨hlift, _, _, hX⟩ := y.2
    exact frame_mem D Λ y.1 hX hlift.1 b
  have hyve : ∀ y ∈ Y, ∀ c, (VS D).hT (F0.e c) (yv y.1) = 0 := by
    intro y hy c
    simp only [yv, map_sum, map_smul, smul_eq_mul, hβy y hy]
    rw [← hv c]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hpie : ∀ c x, (VS D).hT (F0.e c) (piL F0.e f x) = (VS D).hT (F0.e c) x := fun c x => by
    simp [piL_apply, map_sub, map_sum, F0.e_iso]
  have hpif : ∀ c x, (VS D).hT (f c) (piL F0.e f x) = 0 := fun c x => by
    simp [piL_apply, map_sub, map_sum, hfe]
  have hpiz : ∀ x, (VS D).hT F0.z (piL F0.e f x) = (VS D).hT F0.z x := fun x => by
    simp [piL_apply, map_sub, map_sum, hze]
  have hι2 : ∀ y : Carrier (PD D Λ (lf D F0) u'), ι2 y.1 ∈ Λ := by
    intro y
    let lam : (VS D).V := ∑ b, ((nv : D.host.E) * v b) • frame y.1 b
    have hlam : lam ∈ Λ := Λ.sum_mem fun b _ => hmemE _ _ (hvint' b) (hyΛ y b)
    have : ι2 y.1 = (nd : D.host.E) • lam - ∑ c, ((nd : D.host.E) * (VS D).hT (f c) lam) • F0.e c := by
      have h1 : (nv : D.host.E) • yv y.1 = lam := by
        simp only [yv, lam, Finset.smul_sum, smul_smul]
      have h2 : ι2 y.1 = (nd : D.host.E) • piL F0.e f lam := by
        simp only [ι2]
        rw [← h1, map_smul, smul_smul]
        push_cast
        ring_nf
      rw [h2, piL_apply, smul_sub]
      congr 1
      rw [Finset.smul_sum]
      simp only [smul_smul]
    rw [this]
    exact Λ.sub_mem (hnat nd _ hlam) (Λ.sum_mem fun c _ => hmemE _ _ (hfint _ hlam c) (he c))
  have hhz : ∀ y ∈ Y, hz y.1 = ((nd * nv : ℕ) : D.host.E) * ∑ b, v b * Z (Fin.last D.R.rS) b := by
    intro y hy
    simp only [hz, ι2, map_smul, smul_eq_mul, hpiz, yv, map_sum, hzy y hy]

  have hyvn : ∀ y : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E),
      (VS D).hT (yv y) (yv y) = (VS D).hT (yv y0.1) (yv y0.1) := by
    intro y
    simp only [yv, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, gram_frame]
  have hpin : ∀ y ∈ Y, (VS D).hT (piL F0.e f (yv y.1)) (piL F0.e f (yv y.1)) = (VS D).hT (yv y.1) (yv y.1) := by
    intro y hy
    have h1 : ∀ c, (VS D).hT (yv y.1) (F0.e c) = 0 := fun c => by rw [← herm_star, hyve y hy c]; simp
    simp [piL_apply, map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
      hyve y hy, h1, F0.e_iso]
  set hzc : D.host.E := ((nd * nv : ℕ) : D.host.E) * ∑ b, v b * Z (Fin.last D.R.rS) b with hzc_def
  set K : D.host.E := ((Tu D u : ℕ) : D.host.E) ^ 2 * ((((nd * nv : ℕ) : D.host.E)) ^ 2 *
      (VS D).hT (yv y0.1) (yv y0.1)) + ((Tu D u : ℕ) : D.host.E) * hzc * star hzc with hK_def
  have hxK : ∀ y ∈ Y, (VS D).hT (xf y.1) (xf y.1) = K := by
    intro y hy
    have hιz : (VS D).hT (ι2 y.1) F0.z = star (hz y.1) := by rw [← herm_star]
    have hιι : (VS D).hT (ι2 y.1) (ι2 y.1) = (((nd * nv : ℕ) : D.host.E)) ^ 2 * (VS D).hT (yv y0.1) (yv y0.1) := by
      simp only [ι2, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply,
        star_natCast, hpin y hy, hyvn]
      ring
    have hzz : (VS D).hT F0.z F0.z = -((Tu D u : ℕ) : D.host.E) := F0.z_norm
    simp only [xf, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, star_natCast, hιz, hιι, hzz]
    have hh : hz y.1 = hzc := hhz y hy
    rw [show (VS D).hT F0.z (ι2 y.1) = hz y.1 from rfl, hh]
    simp only [hK_def]
    ring

  let P : Submodule D.host.E (VS D).V :=
    orth (VS D) (Xplus (lf D F0)) ⊓ ⨅ c, LinearMap.ker ((VS D).hT (f c))
  have hpos : ∀ x ∈ P, x ≠ 0 → ∀ τ : D.host.E →+* ℂ, 0 < (τ ((VS D).hT x x)).re := by
    intro x hx hne τ
    obtain ⟨hxo, hxf⟩ := Submodule.mem_inf.1 hx
    refine PI.UnitaryGroupMassFormula.BetaModX.positive_weight_holds D (Tu D u) (lf D F0) τ x (D.mem u).A.T_prime.pos hxo ?_
    intro hxX
    obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hxX
    apply hne
    have ht : ∀ c, t c = 0 := by
      intro c
      have := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hxf c)
      simpa [map_sum, hfe] using this
    simp [ht]
  have hxP : ∀ y ∈ Y, xf y.1 ∈ P := by
    intro y hy
    refine Submodule.mem_inf.2 ⟨mem_orth_Xplus (lf D F0) _ (fun a => ?_) ?_, (Submodule.mem_iInf _).2 fun c => ?_⟩
    · show (VS D).hT (F0.e a) (xf y.1) = 0
      simp [xf, ι2, map_add, map_smul, hpie, hyve y hy, F0.z_orth]
    · show (VS D).hT F0.z (xf y.1) = 0
      simp only [xf, map_add, map_smul, smul_eq_mul, F0.z_norm]
      change ((Tu D u : ℕ) : D.host.E) * hz y.1 + hz y.1 * -((Tu D u : ℕ) : D.host.E) = 0
      ring
    · rw [LinearMap.mem_ker]
      simp [xf, ι2, map_add, map_smul, hpif, hfz]
  have hxΛ : ∀ y : Carrier (PD D Λ (lf D F0) u'), xf y.1 ∈ Λ := fun y =>
    Λ.add_mem (hnat _ _ (hι2 y)) (hmemE _ _ (hint _ hz0 _ (hι2 y)) hz0)

  haveI := hRfin
  let κ : Carrier (PD D Λ (lf D F0) u') → (VS D).V × (Fin (D.R.rS + 1) → R) :=
    fun y => (xf y.1, fun b => ρ (frame y.1 b))
  have hfinX := hS D.host.E (VS D) Λ hlat P hpos K
  have hκ : κ '' Y ⊆ {x | x ∈ Λ ∧ x ∈ P ∧ (VS D).hT x x = K} ×ˢ Set.univ := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨hxΛ y, hxP y hy, hxK y hy⟩, trivial⟩
  have hκfin : (κ '' Y).Finite := (hfinX.prod Set.finite_univ).subset hκ
  have hzt : ∀ y : Carrier (PD D Λ (lf D F0) u'), y.1.zt = frame y.1 (Fin.last D.R.rS) := by
    intro y
    rw [y.2.1.2]
    simp [frame, FlagG.fvec]
  have hrel : ∀ y1 ∈ Y, ∀ y2 ∈ Y, κ y1 = κ y2 →
      mk Λ (lf D F0) (PD D Λ (lf D F0) u') y1 = mk Λ (lf D F0) (PD D Λ (lf D F0) u') y2 := by
    intro y1 hy1 y2 hy2 hκ12
    have hx : xf y1.1 = xf y2.1 := congrArg Prod.fst hκ12
    have hr : ∀ b, ρ (frame y1.1 b) = ρ (frame y2.1 b) := fun b => congrFun (congrArg Prod.snd hκ12) b
    have hδ : ∀ b, ∃ lam ∈ Λ, frame y2.1 b - frame y1.1 b = (((nd * nQ) ^ 2 : ℕ) : D.host.E) • lam :=
      fun b => hρ _ (hyΛ y1 b) _ (hyΛ y2 b) (hr b)
    have hι : piL F0.e f (∑ b, v b • frame y1.1 b) = piL F0.e f (∑ b, v b • frame y2.1 b) := by
      have h1 : ((Tu D u : ℕ) : D.host.E) • ι2 y1.1 = ((Tu D u : ℕ) : D.host.E) • ι2 y2.1 := by
        have := hx
        simp only [xf] at this
        rw [show hz y1.1 = hzc from hhz y1 hy1, show hz y2.1 = hzc from hhz y2 hy2] at this
        exact add_right_cancel this
      have h2 := smul_right_injective (VS D).V hT0 h1
      have hne : ((nd * nv : ℕ) : D.host.E) ≠ 0 := by
        have : 0 < nd * nv := Nat.mul_pos hnd hnv
        exact_mod_cast this.ne'
      exact smul_right_injective (VS D).V hne h2
    exact Quot.sound (related_gen hH hSk Λ (lf D F0) f hint he hef θ hθ nd nQ hfint β Q v l hind hβQ hv hQβ
      hQint' y1.1 y2.1 (hzt y1) (hzt y2) (hyΛ y1) (hβy y1 hy1) (hβy y2 hy2)
      (fun a b => by rw [gram_frame, gram_frame]) hδ hι)
  let g : (VS D).V × (Fin (D.R.rS + 1) → R) → TermQ Λ (lf D F0) (PD D Λ (lf D F0) u') := fun t =>
    if h : ∃ y ∈ Y, κ y = t then mk Λ (lf D F0) (PD D Λ (lf D F0) u') (Classical.choose h)
    else mk Λ (lf D F0) (PD D Λ (lf D F0) u') y0
  refine (hκfin.image g).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨κ y, ⟨y, hy, rfl⟩, ?_⟩
  have h : ∃ y' ∈ Y, κ y' = κ y := ⟨y, hy, rfl⟩
  simp only [g, dif_pos h]
  obtain ⟨hy', hκ'⟩ := Classical.choose_spec h
  exact hrel _ hy' _ hy hκ'

end D7

end PI.TermsAtPtFiniteW
