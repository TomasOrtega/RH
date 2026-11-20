import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfDict
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O} (Bs : FramepfBas W T)

/- English proof (translation)
Set `b' : Fin Bs.r → ↥(W.N T)` to `fun k => ⟨Bs.b k, (Bs.mem k).1⟩`. Establish `hli : LinearIndependent (LetA O n) b'`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `h1 : (0 : W.DD T) = ∑ k, g k • Bs.b k`.

Use `congrArg (fun z : ↥(W.N T) => (z : W.DD T)) hg` as an intermediate fact. Simplify `this.symm` using `[b']`. Take `⟨a, -, hu⟩` from `Bs.uniq 0 (W.N T).zero_mem`. Establish `e` using `(hu g h1).trans (hu 0 (by simp)).symm`. Introduce `k`.

Conclude with `congrFun e k`. Establish `hsp : ⊤ ≤ Submodule.span (LetA O n) (Set.range b')`. Introduce `x _`. Take `⟨a, ha, -⟩` from `Bs.uniq x x.2`. Establish `: x = ∑ k, a k • b' k` using `Subtype.ext (by simpa [b'] using ha)`.

Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Conclude with `⟨Module.Basis.mk hli hsp, fun k => by rw [Module.Basis.mk_apply]⟩`.
-/
theorem framepf_nBasis : ∃ β : Module.Basis (Fin Bs.r) (LetA O n) ↥(W.N T),
    ∀ k, (β k : W.DD T) = Bs.b k := by
  let b' : Fin Bs.r → ↥(W.N T) := fun k => ⟨Bs.b k, (Bs.mem k).1⟩
  have hli : LinearIndependent (LetA O n) b' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : (0 : W.DD T) = ∑ k, g k • Bs.b k := by
      have := congrArg (fun z : ↥(W.N T) => (z : W.DD T)) hg
      simpa [b'] using this.symm
    obtain ⟨a, -, hu⟩ := Bs.uniq 0 (W.N T).zero_mem
    have e := (hu g h1).trans (hu 0 (by simp)).symm
    intro k
    exact congrFun e k
  have hsp : ⊤ ≤ Submodule.span (LetA O n) (Set.range b') := by
    intro x _
    obtain ⟨a, ha, -⟩ := Bs.uniq x x.2
    have : x = ∑ k, a k • b' k := Subtype.ext (by simpa [b'] using ha)
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun k => by rw [Module.Basis.mk_apply]⟩

/- English proof (translation)
Take `⟨β, hβ⟩` from `framepf_nBasis Bs`. Use `⟨(Algebra.TensorProduct.basis W.EE β).map (W.N_base T hT).equiv, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, IsBaseChange.equiv_tmul, one_smul, Submodule.subtype_apply, hβ]`.
-/
theorem framepf_ddBasis (hT : IsCrys PD T.ρ) :
    ∃ β : Module.Basis (Fin Bs.r) W.EE (W.DD T), ∀ k, β k = Bs.b k := by
  obtain ⟨β, hβ⟩ := framepf_nBasis Bs
  refine ⟨(Algebra.TensorProduct.basis W.EE β).map (W.N_base T hT).equiv, fun k => ?_⟩
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, IsBaseChange.equiv_tmul, one_smul,
    Submodule.subtype_apply, hβ]

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨z, hz, rfl⟩` from `hx`. Take `⟨a, ha, -⟩` from `Bs.uniq z hz`. Use `⟨fun k => W.φA (a k), ?_⟩` and prove the remaining obligations.

Rewrite using `[ha, map_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => Formalism.MainNotions.LiftingTheory.wmap_φD_smul W T _ _`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, rfl⟩` from `hx`.

Take `⟨a', rfl⟩` from `hy`. Conclude with `⟨a + a', by simp [add_smul, Finset.sum_add_distrib]⟩`. Consider the case `smul s x _ hx`. Take `⟨a, rfl⟩` from `hx`. Conclude with `⟨fun k => s * a k, by simp [Finset.smul_sum, mul_smul]⟩`.
-/
theorem framepf_φpull_coord {y : W.DD T}
    (hy : y ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T)))) :
    ∃ a : Fin Bs.r → LetA O n, y = ∑ k, a k • W.φD T (Bs.b k) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨a, ha, -⟩ := Bs.uniq z hz
    refine ⟨fun k => W.φA (a k), ?_⟩
    rw [ha, map_sum]
    exact Finset.sum_congr rfl fun k _ => Formalism.MainNotions.LiftingTheory.wmap_φD_smul W T _ _
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨a', rfl⟩ := hy
    exact ⟨a + a', by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul s x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    exact ⟨fun k => s * a k, by simp [Finset.smul_sum, mul_smul]⟩

/- English proof (translation)
Take `⟨β, hβ⟩` from `framepf_ddBasis Bs hT`. Establish `hli : LinearIndependent W.EE fun k => W.φD T (Bs.b k)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg k`. Use `Formalism.MainNotions.LiftingTheory.phii_basis W T hT β g (by simpa only [hβ] using hg)` as an intermediate fact.

Conclude with `congrFun this k`. Establish `hN : ∀ m ∈ W.N T, m ∈ Submodule.span W.EE (Set.range fun k => W.φD T (Bs.b k))`. Introduce `m hm`. Take `⟨k, hk⟩` from `W.N_φinv T m hm`. Take `⟨a, ha⟩` from `framepf_φpull_coord Bs hk`.

Establish `h2 : W.Q ^ k • m ∈ Submodule.span W.EE (Set.range fun k => W.φD T (Bs.b k))`. Establish `e : W.Q ^ k • m = ∑ j, a j • W.φD T (Bs.b j)` using `ha`. Rewrite using `[e]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul W.EE]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Rewrite `h2` using `[← algebraMap_smul W.EE, map_pow]`. Take `⟨u, hu⟩` from `(Formalism.MainNotions.LiftingTheory.liftb_Q_unit W).pow k`. Rewrite `h2` using `[← hu]`. Establish `h3` using `Submodule.smul_mem _ ((u⁻¹ : W.EEˣ) : W.EE) h2`.

Rewrite `h3` using `[smul_smul, Units.inv_mul, one_smul]`. Then use the resulting hypothesis. Establish `hsp : ⊤ ≤ Submodule.span W.EE (Set.range fun k => W.φD T (Bs.b k))`. Introduce `y _`. Conclude with `(W.N_base T hT).inductionOn y (fun y => y ∈ Submodule.span W.EE (Set.range fun k => W.φD T (Bs.b k))) (Submodule.zero_mem _) (fun m => hN m m.2) (fun e y hy => Submodule.smul_mem _ e hy) (fun y₁ y₂ h₁ h₂ => Submodule.add_mem _ h₁ h₂)`. Conclude with `⟨Module.Basis.mk hli hsp, fun k => by rw [Module.Basis.mk_apply]⟩`.
-/
theorem framepf_phiBasis (hT : IsCrys PD T.ρ) :
    ∃ β : Module.Basis (Fin Bs.r) W.EE (W.DD T), ∀ k, β k = W.φD T (Bs.b k) := by
  obtain ⟨β, hβ⟩ := framepf_ddBasis Bs hT
  have hli : LinearIndependent W.EE fun k => W.φD T (Bs.b k) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have := Formalism.MainNotions.LiftingTheory.phii_basis W T hT β g (by simpa only [hβ] using hg)
    exact congrFun this k
  have hN : ∀ m ∈ W.N T, m ∈ Submodule.span W.EE (Set.range fun k => W.φD T (Bs.b k)) := by
    intro m hm
    obtain ⟨k, hk⟩ := W.N_φinv T m hm
    obtain ⟨a, ha⟩ := framepf_φpull_coord Bs hk
    have h2 : W.Q ^ k • m ∈ Submodule.span W.EE (Set.range fun k => W.φD T (Bs.b k)) := by
      have e : W.Q ^ k • m = ∑ j, a j • W.φD T (Bs.b j) := ha
      rw [e]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [← algebraMap_smul W.EE]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    rw [← algebraMap_smul W.EE, map_pow] at h2
    obtain ⟨u, hu⟩ := (Formalism.MainNotions.LiftingTheory.liftb_Q_unit W).pow k
    rw [← hu] at h2
    have h3 := Submodule.smul_mem _ ((u⁻¹ : W.EEˣ) : W.EE) h2
    rwa [smul_smul, Units.inv_mul, one_smul] at h3
  have hsp : ⊤ ≤ Submodule.span W.EE (Set.range fun k => W.φD T (Bs.b k)) := by
    intro y _
    exact (W.N_base T hT).inductionOn y
      (fun y => y ∈ Submodule.span W.EE (Set.range fun k => W.φD T (Bs.b k)))
      (Submodule.zero_mem _) (fun m => hN m m.2) (fun e y hy => Submodule.smul_mem _ e hy)
      (fun y₁ y₂ h₁ h₂ => Submodule.add_mem _ h₁ h₂)
  exact ⟨Module.Basis.mk hli hsp, fun k => by rw [Module.Basis.mk_apply]⟩

/- English proof (translation)
Take `⟨β, hβ⟩` from `framepf_phiBasis Bs hT`. Establish `h0 : ∑ k, algebraMap (LetA O n) W.EE (a k - a' k) • β k = 0`. Simplify using `only [algebraMap_smul, hβ, sub_smul, Finset.sum_sub_distrib, h, sub_self]`. Establish `h1` using `Fintype.linearIndependent_iff.1 β.linearIndependent _ h0`. Use function extensionality and compare the values at `k`.

Conclude with `sub_eq_zero.1 (W.EE_inj ((h1 k).trans (map_zero _).symm))`.
-/
theorem framepf_phi_uniq (hT : IsCrys PD T.ρ) {a a' : Fin Bs.r → LetA O n}
    (h : ∑ k, a k • W.φD T (Bs.b k) = ∑ k, a' k • W.φD T (Bs.b k)) : a = a' := by
  obtain ⟨β, hβ⟩ := framepf_phiBasis Bs hT
  have h0 : ∑ k, algebraMap (LetA O n) W.EE (a k - a' k) • β k = 0 := by
    simp only [algebraMap_smul, hβ, sub_smul, Finset.sum_sub_distrib, h, sub_self]
  have h1 := Fintype.linearIndependent_iff.1 β.linearIndependent _ h0
  funext k
  exact sub_eq_zero.1 (W.EE_inj ((h1 k).trans (map_zero _).symm))

/- English proof (translation)
Take `⟨a, ha⟩` from `framepf_φpull_coord Bs hy`. Use `⟨a, fun k δ hδ => ?_, fun k => ?_, ha⟩` and prove the remaining obligations. Establish `e : ∑ j, W.γA δ (a j) • W.φD T (Bs.b j) = ∑ j, a j • W.φD T (Bs.b j)`. Rewrite using `[← ha, ← hΔ δ hδ]`. Use `conv_rhs => rw [ha, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Formalism.MainNotions.LiftingTheory.wmap_γD_smul, ← W.φγ_comm, (Bs.mem j).2 δ hδ]`. Conclude with `congrFun (framepf_phi_uniq Bs hT e) k`. Establish `e : ∑ j, ((letE c : LetA O n) * a j) • W.φD T (Bs.b j) = ∑ j, a j • W.φD T (Bs.b j)`. Rewrite using `[← ha, ← hc]`.

Use `conv_rhs => rw [ha, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_smul _ _ _`. Conclude with `congrFun (framepf_phi_uniq Bs hT e) k`.
-/
theorem framepf_phi_coordΔ (hT : IsCrys PD T.ρ) (c : ZMod n) {y : W.DD T}
    (hy : y ∈ Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))))
    (hΔ : ∀ δ ∈ W.DelF, W.γD T δ y = y) (hc : (letE c : LetA O n) • y = y) :
    ∃ a : Fin Bs.r → LetA O n, (∀ k, a k ∈ W.AΔ) ∧ (∀ k, (letE c : LetA O n) * a k = a k) ∧
      y = ∑ k, a k • W.φD T (Bs.b k) := by
  obtain ⟨a, ha⟩ := framepf_φpull_coord Bs hy
  refine ⟨a, fun k δ hδ => ?_, fun k => ?_, ha⟩
  · have e : ∑ j, W.γA δ (a j) • W.φD T (Bs.b j) = ∑ j, a j • W.φD T (Bs.b j) := by
      rw [← ha, ← hΔ δ hδ]
      conv_rhs => rw [ha, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, ← W.φγ_comm, (Bs.mem j).2 δ hδ]
    exact congrFun (framepf_phi_uniq Bs hT e) k
  · have e : ∑ j, ((letE c : LetA O n) * a j) • W.φD T (Bs.b j) = ∑ j, a j • W.φD T (Bs.b j) := by
      rw [← ha, ← hc]
      conv_rhs => rw [ha, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
    exact congrFun (framepf_phi_uniq Bs hT e) k

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun _ hx => Formalism.MainNotions.LiftingTheory.wmap_Nl_le W T i hx)`.
-/
theorem framepf_φspan_le (i : ZMod n) : Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T i) ≤
    Submodule.span (LetA O n) (W.φD T '' (W.N T : Set (W.DD T))) :=
  Submodule.span_mono (Set.image_mono fun _ hx => Formalism.MainNotions.LiftingTheory.wmap_Nl_le W T i hx)

/- English proof (translation)
Take `⟨⟨h1, h2⟩, h3⟩` from `hy`. Conclude with `framepf_phi_coordΔ Bs hT c (framepf_φspan_le (c - 1) h1) ((mem_DelS W T y).1 h2) ((mem_letS W T c y).1 h3)`.
-/
theorem framepf_Pc_coord (hT : IsCrys PD T.ρ) (c : ZMod n) (y : W.DD T) (hy : y ∈ PcS W T c) :
    ∃ a : Fin Bs.r → LetA O n, (∀ k, a k ∈ W.AΔ) ∧ (∀ k, (letE c : LetA O n) * a k = a k) ∧
      y = ∑ k, a k • W.φD T (Bs.b k) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hy
  exact framepf_phi_coordΔ Bs hT c (framepf_φspan_le (c - 1) h1) ((mem_DelS W T y).1 h2)
    ((mem_letS W T c y).1 h3)

/- English proof (translation)
Use `Submodule.sum_mem _ fun k _ => ⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show a k • W.φD T (Bs.b k) ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))`. Rewrite using `[← hc k, mul_comm, mul_smul, ← φD_letE]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨Bs.b k, (Bs.mem k).1, rfl⟩, rfl⟩)`. Use `show a k • W.φD T (Bs.b k) ∈ DelS W T`.

Rewrite using `[mem_DelS]`. Introduce `δ hδ`. Rewrite using `[Formalism.MainNotions.LiftingTheory.wmap_γD_smul, ← W.φγ_comm, (Bs.mem k).2 δ hδ, ha k δ hδ]`. Use `show a k • W.φD T (Bs.b k) ∈ letS W T c`. Rewrite using `[mem_letS, smul_smul, hc k]`.
-/
theorem framepf_mem_Pc (c : ZMod n) (a : Fin Bs.r → LetA O n) (ha : ∀ k, a k ∈ W.AΔ)
    (hc : ∀ k, (letE c : LetA O n) * a k = a k) : ∑ k, a k • W.φD T (Bs.b k) ∈ PcS W T c := by
  refine Submodule.sum_mem _ fun k _ => ⟨⟨?_, ?_⟩, ?_⟩
  · show a k • W.φD T (Bs.b k) ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))
    rw [← hc k, mul_comm, mul_smul, ← φD_letE]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨Bs.b k, (Bs.mem k).1, rfl⟩, rfl⟩)
  · show a k • W.φD T (Bs.b k) ∈ DelS W T
    rw [mem_DelS]
    intro δ hδ
    rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, ← W.φγ_comm, (Bs.mem k).2 δ hδ, ha k δ hδ]
  · show a k • W.φD T (Bs.b k) ∈ letS W T c
    rw [mem_letS, smul_smul, hc k]

end Local

end Formalism.MainNotions.N.Ln34

end
