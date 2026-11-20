import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinrankLjjSpan

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

/- English proof (translation)
Set `W : Submodule ℚ_[p] (MvPolynomial (GM.M.BVar N r D.T.t) ℚ_[p])` to `Submodule.span ℚ_[p] (SetLike.coe (Ljj (r := r) p (gmB D) j jp))`. Use `haveI hWfd : FiniteDimensional ℚ_[p] W := Ljj_span_fd (p := p) (r := r) (gmB D) j jp`. Set `Pk : MvPolynomial (BVar N r D.T.t) (KK O)` to `((∏ i : Fin D.T.t, BlockData.Ehat (r := r) O D i ^ j i) * BlockData.Eplus (r := r) O D ^ jp * ∏ i : Fin D.T.t, MvPolynomial.X (scalZ N r D.T.t i.castSucc) ^ D.T.z i) * MvPolynomial.X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus`. Set `mι : MvPolynomial (GM.M.BVar N r D.T.t) ℚ_[p] →+* MvPolynomial (BVar N r D.T.t) (KK O)` to `MvPolynomial.map ι`. Set `fA : MvPolynomial (GM.M.BVar N r D.T.t) ℚ_[p] →+ MvPolynomial (BVar N r D.T.t) (KK O)` to `(AddMonoidHom.mulLeft Pk).comp mι.toAddMonoidHom`.

Establish `hfA : ∀ u, fA u = Pk * mι u` using `fun u => rfl`. Establish `hadd : ∀ u v, fA (u + v) = fA u + fA v` using `fun u v => map_add fA u v`. Establish `hsmul : ∀ (c : ℚ_[p]) u, fA (c • u) = ι c • fA u`. Introduce `c u`. Rewrite using `[hfA, hfA, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul]`.

Simplify using `only [mι, MvPolynomial.map_C]`. Expand and normalize the polynomial expressions, which then agree. Set `T : Submodule (KK O) (MvPolynomial (BVar N r D.T.t) (KK O))` to `Submodule.span (KK O) (fA '' (W : Set _))`. Establish `hT : Module.finrank (KK O) T ≤ Module.finrank ℚ_[p] W` using `finrank_span_image_le ι fA hadd hsmul W`. Set `bW` to `Module.finBasis ℚ_[p] W`.

Establish `hTle : T ≤ Submodule.span (KK O) (Set.range fun i => fA (bW i : MvPolynomial _ ℚ_[p]))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Establish `hw' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : MvPolynomial _ ℚ_[p])`. Establish `h1 : ((∑ i, (bW.repr ⟨w, hw⟩ i) • bW i : W) : MvPolynomial _ ℚ_[p]) = w`.

Rewrite using `[bW.sum_repr]`. Use `h1.symm.trans ?_` and prove the remaining obligations. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul]`. Rewrite using `[hw', map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hsmul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Use `haveI : FiniteDimensional (KK O) (Submodule.span (KK O) (Set.range fun i => fA (bW i : MvPolynomial _ ℚ_[p]))) := FiniteDimensional.span_of_finite (KK O) (Set.finite_range _)`. Use `haveI : FiniteDimensional (KK O) T := Submodule.finiteDimensional_of_le hTle`. Establish `hbase : ∀ y0 ∈ GM.M.YZ (r` using `r) p ((gmB D).lettersAt j jp) D.T.J D.T.thr, ∀ g0 ∈ GM.M.XiPolZ p N r D.T.t (D.B - jp), Pk * rename (chainEmb N r D.T.t) (MvPolynomial.map ι y0) * MvPolynomial.map ι g0 ∈ T := by`.

Introduce `y0 hy0 g0 hg0`. Establish `h1 : rename (GM.M.chainEmb N r D.T.t) y0 * g0 ∈ Ljj (r` using `r) p (gmB D) j jp := by`. Unfold `Ljj`. Conclude with `Submodule.subset_span ⟨y0, hy0, g0, hg0, rfl⟩`. Establish `hmem : rename (GM.M.chainEmb N r D.T.t) y0 * g0 ∈ W` using `Submodule.subset_span h1`.

Use `Submodule.subset_span (R := KK O) (Set.mem_image_of_mem fA hmem)` as an intermediate fact. Rewrite `this` using `[hfA]`. Simplify using `only [mι, map_mul, MvPolynomial.map_rename] at this`. Rewrite `this` using `[← mul_assoc]`. Conclude with `this`.

Establish `hstep : ∀ a ∈ Submodule.span (KK O) (MvPolynomial.map ι '' (GM.M.YZ (r` using `r) p ((gmB D).lettersAt j jp) D.T.J D.T.thr : Set _)), ∀ c ∈ Submodule.span (KK O) (MvPolynomial.map ι '' (GM.M.XiPolZ p N r D.T.t (D.B - jp) : Set _)), Pk * rename (chainEmb N r D.T.t) a * c ∈ T := by`. Introduce `a ha c hc`. Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem c hc`. Take `⟨g0, hg0, rfl⟩` from `hc`.

Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem a ha`. Take `⟨y0, hy0, rfl⟩` from `ha`. Conclude with `hbase y0 hy0 g0 hg0`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add, mul_add, add_mul]`. Conclude with `T.add_mem hx hy`. Consider the case `smul k x _ hx`. Rewrite using `[map_smul, mul_smul_comm, smul_mul_assoc]`.

Conclude with `T.smul_mem k hx`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[mul_add]`. Conclude with `T.add_mem hx hy`.

Consider the case `smul k x _ hx`. Rewrite using `[mul_smul_comm]`. Conclude with `T.smul_mem k hx`. Establish `hgens : Submodule.span (KK O) (BlockData.gens (r` using `r) O D j jp) ≤ T := by`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `x ⟨y, hy, g, hg, rfl⟩`. Conclude with `hstep _ (hY O p ι N r (D.lettersAt j jp) D.T.q D.T.J D.T.thr y hy) g (xi_span ι g hg)`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem finrank_span_blockData_gens {p : ℕ} [Fact (Nat.Prime p)] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ι : ℚ_[p] →+* KK O) {N r : ℕ} [NeZero r] (hY : RestYbc)
    (D : BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    Module.finrank (KK O) (Submodule.span (KK O) (BlockData.gens (r := r) O D j jp)) ≤
      Module.finrank ℤ_[p] (Ljj (r := r) p (gmB D) j jp) := by
  classical
  let W : Submodule ℚ_[p] (MvPolynomial (GM.M.BVar N r D.T.t) ℚ_[p]) :=
    Submodule.span ℚ_[p] (SetLike.coe (Ljj (r := r) p (gmB D) j jp))
  haveI hWfd : FiniteDimensional ℚ_[p] W := Ljj_span_fd (p := p) (r := r) (gmB D) j jp
  let Pk : MvPolynomial (BVar N r D.T.t) (KK O) :=
    ((∏ i : Fin D.T.t, BlockData.Ehat (r := r) O D i ^ j i) * BlockData.Eplus (r := r) O D ^ jp *
      ∏ i : Fin D.T.t, MvPolynomial.X (scalZ N r D.T.t i.castSucc) ^ D.T.z i) *
      MvPolynomial.X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus
  let mι : MvPolynomial (GM.M.BVar N r D.T.t) ℚ_[p] →+* MvPolynomial (BVar N r D.T.t) (KK O) :=
    MvPolynomial.map ι
  let fA : MvPolynomial (GM.M.BVar N r D.T.t) ℚ_[p] →+ MvPolynomial (BVar N r D.T.t) (KK O) :=
    (AddMonoidHom.mulLeft Pk).comp mι.toAddMonoidHom
  have hfA : ∀ u, fA u = Pk * mι u := fun u => rfl
  have hadd : ∀ u v, fA (u + v) = fA u + fA v := fun u v => map_add fA u v
  have hsmul : ∀ (c : ℚ_[p]) u, fA (c • u) = ι c • fA u := by
    intro c u
    rw [hfA, hfA, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul]
    simp only [mι, MvPolynomial.map_C]
    ring
  let T : Submodule (KK O) (MvPolynomial (BVar N r D.T.t) (KK O)) :=
    Submodule.span (KK O) (fA '' (W : Set _))
  have hT : Module.finrank (KK O) T ≤ Module.finrank ℚ_[p] W :=
    finrank_span_image_le ι fA hadd hsmul W
  let bW := Module.finBasis ℚ_[p] W
  have hTle : T ≤ Submodule.span (KK O) (Set.range fun i => fA (bW i : MvPolynomial _ ℚ_[p])) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : MvPolynomial _ ℚ_[p]) := by
      have h1 : ((∑ i, (bW.repr ⟨w, hw⟩ i) • bW i : W) : MvPolynomial _ ℚ_[p]) = w := by
        rw [bW.sum_repr]
      refine h1.symm.trans ?_
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [hw', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : FiniteDimensional (KK O)
      (Submodule.span (KK O) (Set.range fun i => fA (bW i : MvPolynomial _ ℚ_[p]))) :=
    FiniteDimensional.span_of_finite (KK O) (Set.finite_range _)
  haveI : FiniteDimensional (KK O) T :=
    Submodule.finiteDimensional_of_le hTle
  have hbase : ∀ y0 ∈ GM.M.YZ (r := r) p ((gmB D).lettersAt j jp) D.T.J D.T.thr,
      ∀ g0 ∈ GM.M.XiPolZ p N r D.T.t (D.B - jp),
      Pk * rename (chainEmb N r D.T.t) (MvPolynomial.map ι y0) * MvPolynomial.map ι g0 ∈ T := by
    intro y0 hy0 g0 hg0
    have h1 : rename (GM.M.chainEmb N r D.T.t) y0 * g0 ∈ Ljj (r := r) p (gmB D) j jp := by
      unfold Ljj
      exact Submodule.subset_span ⟨y0, hy0, g0, hg0, rfl⟩
    have hmem : rename (GM.M.chainEmb N r D.T.t) y0 * g0 ∈ W := Submodule.subset_span h1
    have := Submodule.subset_span (R := KK O) (Set.mem_image_of_mem fA hmem)
    rw [hfA] at this
    simp only [mι, map_mul, MvPolynomial.map_rename] at this
    rw [← mul_assoc] at this
    exact this
  have hstep : ∀ a ∈ Submodule.span (KK O)
        (MvPolynomial.map ι '' (GM.M.YZ (r := r) p ((gmB D).lettersAt j jp) D.T.J D.T.thr : Set _)),
      ∀ c ∈ Submodule.span (KK O)
        (MvPolynomial.map ι '' (GM.M.XiPolZ p N r D.T.t (D.B - jp) : Set _)),
      Pk * rename (chainEmb N r D.T.t) a * c ∈ T := by
    intro a ha c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨g0, hg0, rfl⟩ := hc
      induction ha using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨y0, hy0, rfl⟩ := ha
        exact hbase y0 hy0 g0 hg0
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add, mul_add, add_mul]
        exact T.add_mem hx hy
      | smul k x _ hx =>
        rw [map_smul, mul_smul_comm, smul_mul_assoc]
        exact T.smul_mem k hx
    | zero => simp
    | add x y _ _ hx hy =>
      rw [mul_add]
      exact T.add_mem hx hy
    | smul k x _ hx =>
      rw [mul_smul_comm]
      exact T.smul_mem k hx
  have hgens : Submodule.span (KK O) (BlockData.gens (r := r) O D j jp) ≤ T := by
    rw [Submodule.span_le]
    rintro x ⟨y, hy, g, hg, rfl⟩
    exact hstep _ (hY O p ι N r (D.lettersAt j jp) D.T.q D.T.J D.T.thr y hy) g (xi_span ι g hg)
  calc Module.finrank (KK O) (Submodule.span (KK O) (BlockData.gens (r := r) O D j jp))
      ≤ Module.finrank (KK O) T :=
        LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hgens)
          (Submodule.inclusion_injective hgens)
    _ ≤ Module.finrank ℚ_[p] W := hT
    _ = Module.finrank ℤ_[p] (Ljj (r := r) p (gmB D) j jp) := (finrank_Ljj_span (gmB D) j jp).symm

/- English proof (translation)
Introduce `aTop _ aPlus _ b _ l _`. Conclude with `finrank_span_blockData_gens (O := X.O) (r := X.r) (iotaX X) hY (blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b) l.1 l.2`.
-/
theorem restBClvl_of (hY : RestYbc) : RestBClvl C0 CE1 CE2 X := by
  intro aTop _ aPlus _ b _ l _
  exact finrank_span_blockData_gens (O := X.O) (r := X.r) (iotaX X) hY
    (blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b) l.1 l.2

end Formalism.MainNotions.G.SymmetricFormBlocks

end
