import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupEigenspaceEqTopOfAeval
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedSpaceLeSupEigenspacesStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

/- English proof (translation)
Set `E : s → Submodule K V` to `fun r => f.eigenspace (r : K)`. Establish `hind : iSupIndep E` using `(Module.End.eigenspaces_iSupIndep f).comp Subtype.val_injective`. Establish `htop : iSup E = ⊤`. Rewrite using `[← h, iSup_subtype]`. Establish `hint : DirectSum.IsInternal E` using `(DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top E).mpr ⟨hind, htop⟩`.

Set `bE : ∀ r : s, Module.Basis (Module.Free.ChooseBasisIndex K (E r)) K (E r)` to `fun r => Module.Free.chooseBasis K (E r)`. Set `bb` to `hint.collectedBasis bE`. Establish `hdiag : LinearMap.toMatrix bb bb f = Matrix.diagonal (fun x => ((x.1 : s) : K))`. Use extensionality with `x y`. Rewrite using `[LinearMap.toMatrix_apply]`.

Establish `hy : (bb y : V) = (bE y.1 y.2 : V)`. Rewrite using `[hint.collectedBasis_coe]`. Establish `hev : f (bE y.1 y.2 : V) = ((y.1 : s) : K) • (bE y.1 y.2 : V)` using `Module.End.mem_eigenspace_iff.mp (bE y.1 y.2).2`. Rewrite using `[hy, hev, ← hy, map_smul, bb.repr_self, Matrix.diagonal_apply]`. Distinguish the cases in `hxy : x = y`.

Substitute `hxy` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hxy), if_neg hxy, smul_zero]`. Use `⟨Finset.univ.val.map (fun x : (Σ r : s, Module.Free.ChooseBasisIndex K (E r)) => ((x.1 : s) : K)), ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.charpoly_toMatrix f bb, hdiag, Matrix.charpoly_diagonal, Multiset.map_map, Finset.prod_eq_multiset_prod]`.

Both sides reduce to the same expression.
-/
theorem charpoly_eq_prod_of_iSup_eigenspace {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (s : Finset K)
    (h : ⨆ r ∈ s, f.eigenspace r = ⊤) :
    ∃ m : Multiset K, f.charpoly = (m.map fun a => X - C a).prod := by
  classical
  let E : s → Submodule K V := fun r => f.eigenspace (r : K)
  have hind : iSupIndep E := (Module.End.eigenspaces_iSupIndep f).comp Subtype.val_injective
  have htop : iSup E = ⊤ := by
    rw [← h, iSup_subtype]
  have hint : DirectSum.IsInternal E :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top E).mpr ⟨hind, htop⟩
  let bE : ∀ r : s, Module.Basis (Module.Free.ChooseBasisIndex K (E r)) K (E r) :=
    fun r => Module.Free.chooseBasis K (E r)
  let bb := hint.collectedBasis bE
  have hdiag : LinearMap.toMatrix bb bb f = Matrix.diagonal (fun x => ((x.1 : s) : K)) := by
    ext x y
    rw [LinearMap.toMatrix_apply]
    have hy : (bb y : V) = (bE y.1 y.2 : V) := by
      rw [hint.collectedBasis_coe]
    have hev : f (bE y.1 y.2 : V) = ((y.1 : s) : K) • (bE y.1 y.2 : V) :=
      Module.End.mem_eigenspace_iff.mp (bE y.1 y.2).2
    rw [hy, hev, ← hy, map_smul, bb.repr_self, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hxy), if_neg hxy, smul_zero]
  refine ⟨Finset.univ.val.map (fun x : (Σ r : s, Module.Free.ChooseBasisIndex K (E r)) => ((x.1 : s) : K)), ?_⟩
  rw [← LinearMap.charpoly_toMatrix f bb, hdiag, Matrix.charpoly_diagonal, Multiset.map_map,
    Finset.prod_eq_multiset_prod]
  rfl

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis O B`. Set `v : Module.Free.ChooseBasisIndex O B → V` to `fun i => (b i : V)`. Establish `hliO : LinearIndependent O v` using `b.linearIndependent.map' B.subtype (Submodule.ker_subtype B)`. Establish `hli : LinearIndependent (FractionRing O) v` using `(LinearIndependent.iff_fractionRing O (FractionRing O)).mp hliO`. Set `V'` to `Submodule.span (FractionRing O) (Set.range v)`.

Establish `hBV : ∀ x ∈ B, x ∈ V'`. Introduce `x hx`. Establish `h1 : (⟨x, hx⟩ : B) ∈ Submodule.span O (Set.range b)` using `b.span_eq ▸ Submodule.mem_top`. Establish `h2` using `Submodule.mem_map_of_mem (f := B.subtype) h1`. Rewrite `h2` using `[Submodule.map_span, ← Set.range_comp]`.

Conclude with `Submodule.span_le_restrictScalars O (FractionRing O) _ h2`. Establish `hV' : ∀ x ∈ V', f x ∈ V'`. Introduce `x hx`. Use `Submodule.span_induction (p := fun x _ => f x ∈ V') ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `hBV _ (hf _ (b i).2)`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `V'.add_mem hx hy`.

Introduce `a x _ hx`. Rewrite using `[map_smul]`. Conclude with `V'.smul_mem a hx`. Set `f'` to `f.restrict hV'`. Set `bK : Module.Basis (Module.Free.ChooseBasisIndex O B) (FractionRing O) V'` to `Module.Basis.span hli`.

Use `haveI : FiniteDimensional (FractionRing O) V' := Module.Finite.of_basis bK`. Use `set g := (f.restrictScalars O).restrict hf with hgdef`. Establish `hmat : LinearMap.toMatrix bK bK f' = (LinearMap.toMatrix b b g).map (algebraMap O (FractionRing O))`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]`.

Establish `hg : (g (b j) : V) = ∑ i, b.repr (g (b j)) i • v i`. Combine the equalities or inequalities in the displayed calculation. Establish `hf' : f' (bK j) = ∑ i, algebraMap O (FractionRing O) (b.repr (g (b j)) i) • bK i`. Establish `hbK : ∀ i, (bK i : V) = v i` using `fun i => by rw [Module.Basis.span_apply]`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [f', LinearMap.restrict_apply, Submodule.coe_sum, Submodule.coe_smul]`. Repeatedly rewrite using `[hbK]`. Rewrite using `[show f (v j) = (g (b j) : V) from rfl, hg]`. Simplify using `[algebraMap_smul]`. Rewrite using `[hf', bK.repr_sum_self]`.

Establish `hcp : (LinearMap.charpoly g).map (algebraMap O (FractionRing O)) = f'.charpoly`. Rewrite using `[← LinearMap.charpoly_toMatrix g b, ← Matrix.charpoly_map, ← hmat, LinearMap.charpoly_toMatrix]`. Rewrite using `[hcp]`. Apply `charpoly_eq_prod_of_iSup_eigenspace f' s` to reduce the goal to its premises. Establish `hle : V' ≤ LinearMap.ker (aeval f (∏ r ∈ s, (X - C r)))`.

Rewrite using `[GlobalTheory.JointDiag.ker_prod, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hs _ (b i).2`. Rewrite using `[← GlobalTheory.JointDiag.ker_prod, LinearMap.ker_eq_top]`. Use extensionality with `y`.

Rewrite using `[LinearMap.zero_apply, ZeroMemClass.coe_zero, GlobalTheory.JointDiag.aeval_restrict_coe]`. Conclude with `hle y.2`.
-/
theorem charpoly_restrict_map_eq_prod {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V]
    [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
    (B : Submodule O V) [Module.Free O B] [Module.Finite O B] (f : Module.End (FractionRing O) V)
    (hf : ∀ x ∈ B, f x ∈ B) (s : Finset (FractionRing O))
    (hs : ∀ x ∈ B, x ∈ ⨆ r ∈ s, f.eigenspace r) :
    ∃ m : Multiset (FractionRing O), (LinearMap.charpoly ((f.restrictScalars O).restrict hf)).map
      (algebraMap O (FractionRing O)) = (m.map fun a => X - C a).prod := by
  classical
  let b := Module.Free.chooseBasis O B
  let v : Module.Free.ChooseBasisIndex O B → V := fun i => (b i : V)
  have hliO : LinearIndependent O v := b.linearIndependent.map' B.subtype (Submodule.ker_subtype B)
  have hli : LinearIndependent (FractionRing O) v :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).mp hliO
  let V' := Submodule.span (FractionRing O) (Set.range v)
  have hBV : ∀ x ∈ B, x ∈ V' := by
    intro x hx
    have h1 : (⟨x, hx⟩ : B) ∈ Submodule.span O (Set.range b) := b.span_eq ▸ Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := B.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact Submodule.span_le_restrictScalars O (FractionRing O) _ h2
  have hV' : ∀ x ∈ V', f x ∈ V' := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => f x ∈ V') ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      exact hBV _ (hf _ (b i).2)
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact V'.add_mem hx hy
    · intro a x _ hx
      rw [map_smul]
      exact V'.smul_mem a hx
  let f' := f.restrict hV'
  let bK : Module.Basis (Module.Free.ChooseBasisIndex O B) (FractionRing O) V' := Module.Basis.span hli
  haveI : FiniteDimensional (FractionRing O) V' := Module.Finite.of_basis bK
  set g := (f.restrictScalars O).restrict hf with hgdef
  have hmat : LinearMap.toMatrix bK bK f' = (LinearMap.toMatrix b b g).map (algebraMap O (FractionRing O)) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have hg : (g (b j) : V) = ∑ i, b.repr (g (b j)) i • v i := by
      calc (g (b j) : V) = ((∑ i, b.repr (g (b j)) i • b i : B) : V) := by rw [b.sum_repr]
        _ = ∑ i, b.repr (g (b j)) i • v i := by simp only [Submodule.coe_sum, Submodule.coe_smul]; rfl
    have hf' : f' (bK j) = ∑ i, algebraMap O (FractionRing O) (b.repr (g (b j)) i) • bK i := by
      have hbK : ∀ i, (bK i : V) = v i := fun i => by rw [Module.Basis.span_apply]
      apply Subtype.ext
      simp only [f', LinearMap.restrict_apply, Submodule.coe_sum, Submodule.coe_smul]
      simp_rw [hbK]
      rw [show f (v j) = (g (b j) : V) from rfl, hg]
      simp [algebraMap_smul]
    rw [hf', bK.repr_sum_self]
  have hcp : (LinearMap.charpoly g).map (algebraMap O (FractionRing O)) = f'.charpoly := by
    rw [← LinearMap.charpoly_toMatrix g b, ← Matrix.charpoly_map, ← hmat, LinearMap.charpoly_toMatrix]
  rw [hcp]
  apply charpoly_eq_prod_of_iSup_eigenspace f' s
  have hle : V' ≤ LinearMap.ker (aeval f (∏ r ∈ s, (X - C r))) := by
    rw [GlobalTheory.JointDiag.ker_prod, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hs _ (b i).2
  rw [← GlobalTheory.JointDiag.ker_prod, LinearMap.ker_eq_top]
  ext y
  rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, GlobalTheory.JointDiag.aeval_restrict_coe]
  exact hle y.2

end GlobalTheory.HeightCounting.FormsStep

namespace GlobalTheory.HeightCounting.FormsStep

/- English proof (translation)
Introduce `D cf jE A S In b0 b1 Sx T Sp hSb hstar hst i j b k P hfr hfi hP`. Distinguish the cases in `hc : HkCond D T i j k P`. Establish `hB : ∀ x ∈ BI D T S In i j b, x ∈ V0T D T S In.rho In.chi In.θ i j b` using `fun x hx => hx.2`. Establish `hL1` using `GlobalTheory.T.fixed_space_le_sup_eigenspaces D cf jE A S In b0 b1 Sx T Sp hSb hstar i j b k P hc`. Set `ev : D.what₂.FT → FractionRing (T.O i)` to `fun σ => algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)`.

Set `sG : Finset D.what₂.FT` to `Finset.univ.filter fun σ : D.what₂.FT => D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ`. Establish `hle : (⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}, Module.End.eigenspace (hkT D T S In i j b k P) (ev σ)) ≤ ⨆ r ∈ sG.image ev, Module.End.eigenspace (hkT D T S In i j b k P) r` using `iSup₂_le fun σ hσ => le_iSup₂_of_le (ev σ) (Finset.mem_image_of_mem ev (by simpa [sG] using hσ)) le_rfl`. Take `⟨m, hm⟩` from `charpoly_restrict_map_eq_prod (BI D T S In i j b) (hkT D T S In i j b k P) (fun x hx => hst i j b k P hc x hx) (sG.image ev) (fun x hx => hle (hL1 (hB x hx)))`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `he : hkB D T S In hst i j b k P = ((hkT D T S In i j b k P).restrictScalars (T.O i)).restrict (fun x hx => hst i j b k P hc x hx)`.

Unfold `hkB`. Rewrite using `[dif_pos hc]`. Rewrite using `[he]`. Conclude with `hm`. Establish `he : hkB D T S In hst i j b k P = 1`.

Unfold `hkB`. Rewrite using `[dif_neg hc]`. Use `⟨Multiset.replicate (Module.finrank (T.O i) ↥(BI D T S In i j b)) 1, ?_⟩` and prove the remaining obligations. Rewrite using `[he, LinearMap.charpoly_one, Multiset.map_replicate, Multiset.prod_replicate, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, map_one]`.
-/
theorem hkB_charpoly_splits : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (hst : HkStab D T S In) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host)
      [hfr : Module.Free (T.O i) ↥(BI D T S In i j b)] [hfi : Module.Finite (T.O i) ↥(BI D T S In i j b)], P ∉ T.S0 i →
      ∃ s : Multiset (FractionRing (T.O i)),
        (LinearMap.charpoly (hkB D T S In hst i j b k P)).map
          (algebraMap (T.O i) (FractionRing (T.O i))) = (s.map fun a => X - C a).prod := by
  classical
  intro D cf jE A S In b0 b1 Sx T Sp hSb hstar hst i j b k P hfr hfi hP
  by_cases hc : HkCond D T i j k P
  · have hB : ∀ x ∈ BI D T S In i j b, x ∈ V0T D T S In.rho In.chi In.θ i j b := fun x hx => hx.2
    have hL1 := GlobalTheory.T.fixed_space_le_sup_eigenspaces D cf jE A S In b0 b1 Sx T Sp hSb hstar i j b k P hc
    let ev : D.what₂.FT → FractionRing (T.O i) := fun σ =>
      algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)
    let sG : Finset D.what₂.FT := Finset.univ.filter fun σ : D.what₂.FT => D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ
    have hle : (⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
        Module.End.eigenspace (hkT D T S In i j b k P) (ev σ)) ≤
        ⨆ r ∈ sG.image ev, Module.End.eigenspace (hkT D T S In i j b k P) r :=
      iSup₂_le fun σ hσ => le_iSup₂_of_le (ev σ) (Finset.mem_image_of_mem ev (by simpa [sG] using hσ)) le_rfl
    obtain ⟨m, hm⟩ := charpoly_restrict_map_eq_prod (BI D T S In i j b) (hkT D T S In i j b k P)
      (fun x hx => hst i j b k P hc x hx) (sG.image ev) (fun x hx => hle (hL1 (hB x hx)))
    refine ⟨m, ?_⟩
    have he : hkB D T S In hst i j b k P = ((hkT D T S In i j b k P).restrictScalars (T.O i)).restrict
        (fun x hx => hst i j b k P hc x hx) := by
      unfold hkB
      rw [dif_pos hc]
    rw [he]
    exact hm
  · have he : hkB D T S In hst i j b k P = 1 := by
      unfold hkB
      rw [dif_neg hc]
    refine ⟨Multiset.replicate (Module.finrank (T.O i) ↥(BI D T S In i j b)) 1, ?_⟩
    rw [he, LinearMap.charpoly_one, Multiset.map_replicate, Multiset.prod_replicate, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, map_one]

end GlobalTheory.HeightCounting.FormsStep
