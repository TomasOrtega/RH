import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsVecOfHermRep
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardStabilizerAutSub
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsRepsOfCover
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ClassRepsDefinite
import Lemmata.GeneralBFactSecondForm.Imports

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace StabilizerLattices

section One

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Introduce `x hx`. Establish `hp` using `hd x hx`. Establish `ht` using `trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := h x x)`. Establish `hre` using `congrArg Complex.re ht`. Rewrite `hre` using `[Complex.re_sum]`.

Establish `hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re` using `Finset.sum_pos (fun σ _ => hp σ.toRingHom) ⟨(Classical.arbitrary (K →+* ℂ)).toRatAlgHom, Finset.mem_univ _⟩`. Rewrite `hpos` using `[← hre]`. Establish `: (algebraMap ℚ ℂ (Algebra.trace ℚ K (h x x))).re = ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ)`. Simplify using the standard rewrite rules. Rewrite `hpos` using `[this]`.

Conclude with `hpos` after adjusting the coercions.
-/
theorem trace_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) :
    ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
  intro x hx
  have hp := hd x hx
  have ht := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := h x x)
  have hre := congrArg Complex.re ht
  rw [Complex.re_sum] at hre
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re :=
    Finset.sum_pos (fun σ _ => hp σ.toRingHom)
      ⟨(Classical.arbitrary (K →+* ℂ)).toRatAlgHom, Finset.mem_univ _⟩
  rw [← hre] at hpos
  have : (algebraMap ℚ ℂ (Algebra.trace ℚ K (h x x))).re = ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) := by
    simp
  rw [this] at hpos
  exact_mod_cast hpos

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_second_form.goal1 .. | (apply Bl.general_b_fact_second_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_form.goal1 <;> assumption)`.
-/
theorem exists_smul_mem {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (v : V) :
    ∃ r : 𝓞 K, r ≠ 0 ∧ r • v ∈ Λ := by
  first | exact Bl.general_b_fact_second_form.goal1 .. | (apply Bl.general_b_fact_second_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_form.goal1 <;> assumption)

scoped instance latAct (h : V →ₗ⋆[K] V →ₗ[K] K) :
    MulAction (Formalism.HermitianLatticesTheory.isom h) (Submodule (𝓞 K) V) where
  smul g Λ := Formalism.HermitianLatticesTheory.gmap g.1 Λ
  one_smul := autSub_gmap_one
  mul_smul a b Λ := autSub_gmap_mul a.1 b.1 Λ

variable {h : V →ₗ⋆[K] V →ₗ[K] K}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_lat (g : Formalism.HermitianLatticesTheory.isom h) (Λ : Submodule (𝓞 K) V) : g • Λ = Formalism.HermitianLatticesTheory.gmap g.1 Λ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_vec (g : Formalism.HermitianLatticesTheory.isom h) (x : V) : g • x = g.1 x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_pair (g : Formalism.HermitianLatticesTheory.isom h) (p : Submodule (𝓞 K) V × V) :
    g • p = (Formalism.HermitianLatticesTheory.gmap g.1 p.1, g.1 p.2) := rfl

def stabLatEquiv (Λ : Submodule (𝓞 K) V) :
    MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) Λ ≃ Formalism.ThetaLiftIndependence.autL h Λ where
  toFun a := ⟨a.1.1, a.1.2, MulAction.mem_stabilizer_iff.mp a.2⟩
  invFun b := ⟨⟨b.1, b.2.1⟩, MulAction.mem_stabilizer_iff.mpr b.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def pairs (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (n : K) :
    Set (Submodule (𝓞 K) V × V) :=
  {p | p.1 ∈ Formalism.HermitianLatticesTheory.genus h L ∧ p.2 ∈ p.1 ∧ h p.2 p.2 = n}

/- English proof (translation)
Rewrite using `[Formalism.HermitianLatticesTheory.isomAct_mem_gmap, LinearEquiv.symm_apply_apply]`. Conclude with `hx`.
-/
theorem apply_mem_gmap (g : V ≃ₗ[K] V) {Λ : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Λ) :
    g x ∈ Formalism.HermitianLatticesTheory.gmap g Λ := by
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, LinearEquiv.symm_apply_apply]
  exact hx

/- English proof (translation)
Assemble the required witnesses or components as `⟨OrbitRepresentatives.gmap_mem_genus hs hp.1 g.2, apply_mem_gmap g.1 hp.2.1, (g.2 p.2 p.2).trans hp.2.2⟩`.
-/
theorem pairs_stable (hs : h.IsSymm) (L : Submodule (𝓞 K) V) (n : K) (g : Formalism.HermitianLatticesTheory.isom h)
    (p : Submodule (𝓞 K) V × V) (hp : p ∈ pairs h L n) : g • p ∈ pairs h L n :=
  ⟨OrbitRepresentatives.gmap_mem_genus hs hp.1 g.2, apply_mem_gmap g.1 hp.2.1, (g.2 p.2 p.2).trans hp.2.2⟩

def perpO (h : V →ₗ⋆[K] V →ₗ[K] K) (x : V) : Submodule (𝓞 K) V :=
  (LinearMap.ker (h x)).restrictScalars (𝓞 K)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_perpO (x v : V) : v ∈ perpO h x ↔ h x v = 0 := Iff.rfl

def proj (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Submodule (𝓞 K) V × V) : Submodule (𝓞 K) V × V :=
  (p.1 ⊓ perpO h p.2, p.2)

/- English proof (translation)
Use `Prod.ext ?_ rfl` and prove the remaining obligations. Use extensionality with `v`. Express the relevant statement in the definitionally equal form `v ∈ Formalism.HermitianLatticesTheory.gmap g.1 p.1 ⊓ perpO h (g.1 p.2) ↔ v ∈ Formalism.HermitianLatticesTheory.gmap g.1 (p.1 ⊓ perpO h p.2)`. Rewrite using `[Submodule.mem_inf, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Submodule.mem_inf, mem_perpO, mem_perpO]`. Establish `: h (g.1 p.2) v = h p.2 (g.1.symm v)` using `by conv_lhs => rw [← LinearEquiv.apply_symm_apply g.1 v]`.

Conclude with `g.2 _ _`. Rewrite using `[this]`.
-/
theorem proj_smul (g : Formalism.HermitianLatticesTheory.isom h) (p : Submodule (𝓞 K) V × V) :
    proj h (g • p) = g • proj h p := by
  refine Prod.ext ?_ rfl
  ext v
  change v ∈ Formalism.HermitianLatticesTheory.gmap g.1 p.1 ⊓ perpO h (g.1 p.2) ↔
    v ∈ Formalism.HermitianLatticesTheory.gmap g.1 (p.1 ⊓ perpO h p.2)
  rw [Submodule.mem_inf, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Submodule.mem_inf,
    mem_perpO, mem_perpO]
  have : h (g.1 p.2) v = h p.2 (g.1.symm v) := by
    conv_lhs => rw [← LinearEquiv.apply_symm_apply g.1 v]
    exact g.2 _ _
  rw [this]

end One

section Two

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open SplitBAux

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `isNoetherian_of_fg_of_noetherian _ hΛ.fg` as an intermediate fact. Establish `hle : (S.cut Λ).map (S.ι.restrictScalars (𝓞 K)) ≤ Λ` using `Submodule.map_comap_le _ _`. Conclude with `Submodule.fg_of_fg_map_injective (S.ι.restrictScalars (𝓞 K)) S.inj (Submodule.FG.of_le_of_isNoetherian hle)`. Rewrite using `[eq_top_iff]`.

Introduce `a _`. Take `⟨r, hr, hra⟩` from `exists_smul_mem hΛ (S.ι a)`. Establish `h1 : r • a ∈ S.cut Λ`. Rewrite using `[VecSplit.mem_cut_iff, ← algebraMap_smul K r a, map_smul, algebraMap_smul]`. Conclude with `hra`.

Establish `hr' : algebraMap (𝓞 K) K r ≠ 0`. Simplify using `using hr`. Establish `e : a = (algebraMap (𝓞 K) K r)⁻¹ • (r • a)`. Rewrite using `[← algebraMap_smul K r a, smul_smul, inv_mul_cancel₀ hr', one_smul]`. Rewrite using `[e]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span h1)`.
-/
theorem isLattice_cut (S : VecSplit h h') {Λ : Submodule (𝓞 K) V}
    (hΛ : Submodule.IsLattice K Λ) : Submodule.IsLattice K (S.cut Λ) := by
  refine ⟨?_, ?_⟩
  · have := isNoetherian_of_fg_of_noetherian _ hΛ.fg
    have hle : (S.cut Λ).map (S.ι.restrictScalars (𝓞 K)) ≤ Λ := Submodule.map_comap_le _ _
    exact Submodule.fg_of_fg_map_injective (S.ι.restrictScalars (𝓞 K)) S.inj
      (Submodule.FG.of_le_of_isNoetherian hle)
  · rw [eq_top_iff]
    intro a _
    obtain ⟨r, hr, hra⟩ := exists_smul_mem hΛ (S.ι a)
    have h1 : r • a ∈ S.cut Λ := by
      rw [VecSplit.mem_cut_iff, ← algebraMap_smul K r a, map_smul, algebraMap_smul]
      exact hra
    have hr' : algebraMap (𝓞 K) K r ≠ 0 := by
      simpa using hr
    have e : a = (algebraMap (𝓞 K) K r)⁻¹ • (r • a) := by
      rw [← algebraMap_smul K r a, smul_smul, inv_mul_cancel₀ hr', one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

def emb (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') : Submodule (𝓞 K) V :=
  Λ'.map (S.ι.restrictScalars (𝓞 K))

/- English proof (translation)
The claim follows from `Submodule.comap_map_eq_of_injective (f := S.ι.restrictScalars (𝓞 K)) S.inj Λ'`.
-/
theorem cut_emb (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') : S.cut (emb S Λ') = Λ' :=
  Submodule.comap_map_eq_of_injective (f := S.ι.restrictScalars (𝓞 K)) S.inj Λ'

/- English proof (translation)
Introduce `A B e` and use `by rw [← cut_emb S A, e, cut_emb]`.
-/
theorem emb_injective (S : VecSplit h h') : Function.Injective (emb S) := fun A B e => by
  rw [← cut_emb S A, e, cut_emb]

/- English proof (translation)
Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hv, hv0⟩`. Take `⟨a, rfl⟩` from `exists_of_orth S hv0`. Conclude with `Submodule.mem_map.mpr ⟨a, hv, rfl⟩`.

Introduce `hv`. Take `⟨a, ha, rfl⟩` from `Submodule.mem_map.mp hv`. Conclude with `⟨ha, S.orth a⟩`.
-/
theorem inf_perpO (S : VecSplit h h') (Λ : Submodule (𝓞 K) V) :
    Λ ⊓ perpO h S.x₀ = emb S (S.cut Λ) := by
  ext v
  constructor
  · rintro ⟨hv, hv0⟩
    obtain ⟨a, rfl⟩ := exists_of_orth S hv0
    exact Submodule.mem_map.mpr ⟨a, hv, rfl⟩
  · intro hv
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hv
    exact ⟨ha, S.orth a⟩

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.gmap emb`. Rewrite using `[← Submodule.map_comp, ← Submodule.map_comp]`. Use `congr 1`. Use extensionality with `a`. Conclude with `extOf_ι S g' a`.
-/
theorem gmap_extOf_emb (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (C : Submodule (𝓞 K) V') :
    Formalism.HermitianLatticesTheory.gmap (extOf S g') (emb S C) = emb S (Formalism.HermitianLatticesTheory.gmap g' C) := by
  unfold Formalism.HermitianLatticesTheory.gmap emb
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext a
  exact extOf_ι S g' a

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[VecSplit.mem_cut_iff, mem_gmap_iff, mem_gmap_iff, VecSplit.mem_cut_iff, eq_decomp_ι S a, extOf_symm_apply, ← eq_decomp_ι]`.
-/
theorem cut_gmap_extOf (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (Λ : Submodule (𝓞 K) V) :
    S.cut (Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) = Formalism.HermitianLatticesTheory.gmap g' (S.cut Λ) := by
  ext a
  rw [VecSplit.mem_cut_iff, mem_gmap_iff, mem_gmap_iff, VecSplit.mem_cut_iff, eq_decomp_ι S a,
    extOf_symm_apply, ← eq_decomp_ι]

/- English proof (translation)
Rewrite using `[MulAction.mem_stabilizer_iff, smul_pair, Prod.ext_iff]`.
-/
theorem stab_pair_iff (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') (g : Formalism.HermitianLatticesTheory.isom h) :
    g ∈ MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) ((emb S Λ', S.x₀) : Submodule (𝓞 K) V × V) ↔
      Formalism.HermitianLatticesTheory.gmap g.1 (emb S Λ') = emb S Λ' ∧ g.1 S.x₀ = S.x₀ := by
  rw [MulAction.mem_stabilizer_iff, smul_pair, Prod.ext_iff]

def stabPairEquiv (hs : h.IsSymm) (S : VecSplit h h') (Λ' : Submodule (𝓞 K) V') :
    MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) ((emb S Λ', S.x₀) : Submodule (𝓞 K) V × V) ≃
      Formalism.ThetaLiftIndependence.autL h' Λ' where
  toFun a := ⟨res S a.1.1 a.1.2 ((stab_pair_iff S Λ' a.1).mp a.2).2,
    res_mem_isom S _ _ _, by
      have := gmap_res S a.1.1 a.1.2 ((stab_pair_iff S Λ' a.1).mp a.2).2
        ((stab_pair_iff S Λ' a.1).mp a.2).1
      rwa [cut_emb] at this⟩
  invFun b := ⟨⟨extOf S b.1, extOf_mem_isom hs S b.2.1⟩, (stab_pair_iff S Λ' _).mpr
    ⟨by rw [gmap_extOf_emb, b.2.2], extOf_x₀ S _⟩⟩
  left_inv a := Subtype.ext (Subtype.ext (LinearEquiv.toLinearMap_injective
    (linearMap_ext S (by simp [extOf_x₀, ((stab_pair_iff S Λ' a.1).mp a.2).2])
      (fun v => by simp [extOf_ι, res_spec]))))
  right_inv b := Subtype.ext (LinearEquiv.ext fun v => S.inj (by simp [res_spec, extOf_ι]))

end Two

end StabilizerLattices

end Formalism.HermitianLattices.Ext.L3
