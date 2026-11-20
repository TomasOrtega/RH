import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq

noncomputable section
open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm.HasLabelling
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp [frameExp]`. Consider the case `succ l ih`. Establish `h1 : frameExp r (l + 1) = frameExp r l + (r + 1 - (l + 1))`. Unfold `frameExp`.

Rewrite using `[Finset.sum_Icc_succ_top (by omega)]`. Establish `h2 : ((r + 1 - (l + 1) : ℕ) : ℤ) = (r : ℤ) - l` using `by omega`. Rewrite using `[h1, Nat.cast_add, ih (by omega), Finset.sum_range_succ, h2]`.
-/
theorem frameExp_cast (r l : ℕ) (hl : l ≤ r + 1) :
    ((frameExp r l : ℕ) : ℤ) = ∑ a ∈ Finset.range l, ((r : ℤ) - a) := by
  induction l with
  | zero => simp [frameExp]
  | succ l ih =>
    have h1 : frameExp r (l + 1) = frameExp r l + (r + 1 - (l + 1)) := by
      unfold frameExp
      rw [Finset.sum_Icc_succ_top (by omega)]
    have h2 : ((r + 1 - (l + 1) : ℕ) : ℤ) = (r : ℤ) - l := by omega
    rw [h1, Nat.cast_add, ih (by omega), Finset.sum_range_succ, h2]

/- English proof (translation)
The claim follows from `|((Algebra.norm ℚ x : ℚ) : ℝ)| * (Ideal.absNorm (dI D) : ℝ) ^ (-(2 * (frameExp r l : ℤ))) := by unfold Nloc rw [map_mul, FractionalIdeal.absNorm_span_singleton (𝓞 D.host.E), map_zpow₀, show ddS D = ((dI D : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.ho …`.
-/
theorem nloc_eq (D : D7) (r l : ℕ) (x : D.host.E) :
    ((Nloc (ddS D) r l x : ℚ) : ℝ) =
      |((Algebra.norm ℚ x : ℚ) : ℝ)| * (Ideal.absNorm (dI D) : ℝ) ^ (-(2 * (frameExp r l : ℤ))) := by
  unfold Nloc
  rw [map_mul, FractionalIdeal.absNorm_span_singleton (𝓞 D.host.E), map_zpow₀,
    show ddS D = ((dI D : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) from rfl,
    FractionalIdeal.coeIdeal_absNorm]
  push_cast
  rfl

/- English proof (translation)
Use `Algebra.norm_eq_of_algEquiv ((starRingAut : D.host.E ≃+* D.host.E).toRatAlgEquiv) x` as an intermediate fact. Simplify using `using this`.
-/
theorem norm_star (D : D7) (x : D.host.E) : Algebra.norm ℚ (star x) = Algebra.norm ℚ x := by
  have := Algebra.norm_eq_of_algEquiv ((starRingAut : D.host.E ≃+* D.host.E).toRatAlgEquiv) x
  simpa using this

/- English proof (translation)
Establish `hA : (Ideal.absNorm (dI D) : ℝ) ≠ 0`. Conclude with `(Ideal.absNorm_eq_zero_iff.not.2 hd)` after adjusting the coercions. Rewrite using `[nloc_eq, mul_ne_zero_iff, abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]`. Simplify using `only [ne_eq, zpow_neg, inv_eq_zero, and_iff_left_iff_imp]`. Introduce `_`.

Conclude with `zpow_ne_zero _ hA`.
-/
theorem nloc_ne_zero (D : D7) (hd : dI D ≠ ⊥) (r l : ℕ) (x : D.host.E) :
    ((Nloc (ddS D) r l x : ℚ) : ℝ) ≠ 0 ↔ x ≠ 0 := by
  have hA : (Ideal.absNorm (dI D) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hd)
  rw [nloc_eq, mul_ne_zero_iff, abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]
  simp only [ne_eq, zpow_neg, inv_eq_zero, and_iff_left_iff_imp]
  intro _
  exact zpow_ne_zero _ hA

/- English proof (translation)
Establish `hX : ∀ w : V, (∀ a : Fin r, H.B (F.e a.castSucc) w = 0) → ∀ y ∈ F.X, H.B y w = 0`. Introduce `w hw y hy`. Establish `hle : F.X ≤ LinearMap.ker (H.B.flip w)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨b, -, rfl⟩`.

Simplify using `using hw b`. Simplify using `using hle hy`. Use `set x := G.e (Fin.last r) - F.e (Fin.last r) with hxdef`. Establish `hxz : H.B x (F.e (Fin.last r)) = 0` using `hX _ F.zperp x h`. Establish `hzx : H.B (F.e (Fin.last r)) x = 0` using `by rw [← H.herm, hxz, star_zero]`.

Establish `hxx : H.B x x = 0`. Use `hX x (fun a => ?_) x h` and prove the remaining obligations. Use `hX (F.e a.castSucc) (fun b => F.iso b a) x h` as an intermediate fact. Rewrite using `[← H.herm, this, star_zero]`. Establish `hG : G.e (Fin.last r) = F.e (Fin.last r) + x` using `by rw [hxdef]; abel`.

Establish `h1` using `G.zz`. Rewrite `h1` using `[hG]`. Simplify using `only [map_add, LinearMap.add_apply, hxz, hzx, hxx, F.zz, add_zero] at h1`. Conclude with `(neg_inj.1 h1).symm`.
-/
theorem T_eq {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
    (F G : Formalism.HermitianLatticeCounting.S6.FlagD H r) (h : G.e (Fin.last r) - F.e (Fin.last r) ∈ F.X) : G.T = F.T := by
  have hX : ∀ w : V, (∀ a : Fin r, H.B (F.e a.castSucc) w = 0) → ∀ y ∈ F.X, H.B y w = 0 := by
    intro w hw y hy
    have hle : F.X ≤ LinearMap.ker (H.B.flip w) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, -, rfl⟩
      simpa using hw b
    simpa using hle hy
  set x := G.e (Fin.last r) - F.e (Fin.last r) with hxdef
  have hxz : H.B x (F.e (Fin.last r)) = 0 := hX _ F.zperp x h
  have hzx : H.B (F.e (Fin.last r)) x = 0 := by rw [← H.herm, hxz, star_zero]
  have hxx : H.B x x = 0 := by
    refine hX x (fun a => ?_) x h
    have := hX (F.e a.castSucc) (fun b => F.iso b a) x h
    rw [← H.herm, this, star_zero]
  have hG : G.e (Fin.last r) = F.e (Fin.last r) + x := by rw [hxdef]; abel
  have h1 := G.zz
  rw [hG] at h1
  simp only [map_add, LinearMap.add_apply, hxz, hzx, hxx, F.zz, add_zero] at h1
  exact (neg_inj.1 h1).symm

end GlobalTheory.TypeAsm.HasLabelling

namespace GlobalTheory.TypeAsm
open GlobalTheory.TypeAsm.HasLabelling
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D large₂ X Y u hS t N hN`. Establish `hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E`. Take `⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩` from `hS`. Conclude with `hH.2.2.2.2.2.2.2`. Take `⟨-, -, -, -, hj, hDl, -, -, -⟩` from `GlobalTheory.DegAsm.adapt_invariants D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) (Ft t) (dI D) N hN`.

Establish `hII : Formalism.HermitianLatticeCounting.S6.II (F0 X u) (Ft t) = Isp (lf D (X.Fu u)).fl (frq X t.rep).fl` using `nf_II _ _ _ _`. Establish `hjT : N.j = jT t` using `by rw [hj, hII]; rfl`. Establish `hjle : jT t ≤ D.R.rS` using `by unfold jT; omega`. Establish `hnf : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1), Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l = star (Formalism.HermitianLatticeCounting.S6.Dl (F0 X u) (Ft t) l hl)` using `fun l hl => nf_Dl _ _ _ _ l hl`. Establish `hd : N.𝔡 = dI D` using `hN.1`.

Establish `hdne : dI D ≠ ⊥` using `hd ▸ N.𝔡_ne`. Establish `key : ∀ l, l ≤ jT t → N.nD l = ((Nloc (ddS D) D.R.rS l (labT t l) : ℚ) : ℝ)`. Introduce `l hl`. Establish `hl' : l ≤ D.R.rS + 1` using `by omega`. Establish `hlab : labT t l = star (Formalism.HermitianLatticeCounting.S6.Dl (F0 X u) (Ft t) l hl')`.

Simplify using `only [labT, if_pos hl]`. Conclude with `hnf l hl'`. Unfold `GlobalTheory.DegCnt.NF.nD`. Rewrite using `[dif_pos hl', hDl l hl', nloc_eq, hlab, norm_star, hd, frameExp_cast _ _ hl']`. Use `⟨hjT, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hz : N.F.e (Fin.last D.R.rS) - (F0 X u).e (Fin.last D.R.rS) ∈ (F0 X u).X` using `hN.2.1 (Fin.last _)`. Establish `h1 : ((N.T : ℕ) : D.host.E) = ((Tu D u : ℕ) : D.host.E)`. Rewrite using `[← N.hT, T_eq (F0 X u) N.F hz]`. Both sides reduce to the same expression. Conclude with `h1` after adjusting the coercions.

Unfold `GlobalTheory.DegCnt.NF.Del`. Rewrite using `[hjT, key _ le_rfl]`. Both sides reduce to the same expression. Unfold `GlobalTheory.DegCnt.NF.Db DbL`. Rewrite using `[hjT]`.

Establish `hset : (Finset.Icc 1 (jT t)).filter (fun l => N.nD l ≠ 0) = k2ends D (jT t) (labT t)`. Use extensionality with `l`. Simplify using `only [k2ends, Finset.mem_filter, Finset.mem_Icc]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`.

Use `⟨⟨h1, h2⟩, ?_⟩` and prove the remaining obligations. Rewrite `h3` using `[key l h2]`. Conclude with `(nloc_ne_zero D hdne _ _ _).1 h3`. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Use `⟨⟨h1, h2⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[key l h2]`. Conclude with `(nloc_ne_zero D hdne _ _ _).2 h3`. Rewrite using `[hset]`. Use `Finset.prod_congr rfl fun l hl => ?_` and prove the remaining obligations. Establish `h2 : l ≤ jT t`.

Simplify using `only [k2ends, Finset.mem_filter, Finset.mem_Icc] at hl`. Conclude with `hl.1.2`. Conclude with `key l h2`. Use function extensionality and compare the values at `l`. Unfold `GlobalTheory.DegAsm.lab`.

Distinguish the cases in `hl : l ≤ jT t`. Establish `hl' : l ≤ D.R.rS + 1` using `by omega`. Rewrite using `[dif_pos ⟨hl, hl'⟩]`. Simplify using `only [labT, if_pos hl]`. Rewrite using `[hnf l hl', star_star]`.

Rewrite using `[dif_neg (fun h => hl h.1)]`. Simplify using `only [labT, if_neg hl, star_zero]`.
-/
theorem labC : LabC := by
  intro D large₂ X Y u hS t N hN
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := by
    obtain ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩ := hS
    exact hH.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, hj, hDl, -, -, -⟩ :=
    GlobalTheory.DegAsm.adapt_invariants D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) (Ft t) (dI D) N hN
  have hII : Formalism.HermitianLatticeCounting.S6.II (F0 X u) (Ft t) = Isp (lf D (X.Fu u)).fl (frq X t.rep).fl := nf_II _ _ _ _
  have hjT : N.j = jT t := by rw [hj, hII]; rfl
  have hjle : jT t ≤ D.R.rS := by unfold jT; omega
  have hnf : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1),
      Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l = star (Formalism.HermitianLatticeCounting.S6.Dl (F0 X u) (Ft t) l hl) :=
    fun l hl => nf_Dl _ _ _ _ l hl
  have hd : N.𝔡 = dI D := hN.1
  have hdne : dI D ≠ ⊥ := hd ▸ N.𝔡_ne
  have key : ∀ l, l ≤ jT t → N.nD l = ((Nloc (ddS D) D.R.rS l (labT t l) : ℚ) : ℝ) := by
    intro l hl
    have hl' : l ≤ D.R.rS + 1 := by omega
    have hlab : labT t l = star (Formalism.HermitianLatticeCounting.S6.Dl (F0 X u) (Ft t) l hl') := by
      simp only [labT, if_pos hl]
      exact hnf l hl'
    unfold GlobalTheory.DegCnt.NF.nD
    rw [dif_pos hl', hDl l hl', nloc_eq, hlab, norm_star, hd, frameExp_cast _ _ hl']
  refine ⟨hjT, ?_, ?_, ?_, ?_⟩
  · have hz : N.F.e (Fin.last D.R.rS) - (F0 X u).e (Fin.last D.R.rS) ∈ (F0 X u).X := hN.2.1 (Fin.last _)
    have h1 : ((N.T : ℕ) : D.host.E) = ((Tu D u : ℕ) : D.host.E) := by
      rw [← N.hT, T_eq (F0 X u) N.F hz]
      rfl
    exact_mod_cast h1
  · unfold GlobalTheory.DegCnt.NF.Del
    rw [hjT, key _ le_rfl]
    rfl
  · unfold GlobalTheory.DegCnt.NF.Db DbL
    rw [hjT]
    have hset : (Finset.Icc 1 (jT t)).filter (fun l => N.nD l ≠ 0) = k2ends D (jT t) (labT t) := by
      ext l
      simp only [k2ends, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, h2⟩, ?_⟩
        rw [key l h2] at h3
        exact (nloc_ne_zero D hdne _ _ _).1 h3
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, h2⟩, ?_⟩
        rw [key l h2]
        exact (nloc_ne_zero D hdne _ _ _).2 h3
    rw [hset]
    refine Finset.prod_congr rfl fun l hl => ?_
    have h2 : l ≤ jT t := by
      simp only [k2ends, Finset.mem_filter, Finset.mem_Icc] at hl
      exact hl.1.2
    exact key l h2
  · funext l
    unfold GlobalTheory.DegAsm.lab
    by_cases hl : l ≤ jT t
    · have hl' : l ≤ D.R.rS + 1 := by omega
      rw [dif_pos ⟨hl, hl'⟩]
      simp only [labT, if_pos hl]
      rw [hnf l hl', star_star]
    · rw [dif_neg (fun h => hl h.1)]
      simp only [labT, if_neg hl, star_zero]

end GlobalTheory.TypeAsm
