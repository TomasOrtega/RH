import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPhi
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.InvLiftPfA
import Formalism.SharpRestriction.LevelLetterCocycles.ClassMapStep

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}

section Map

variable {T₁ T₂ : LocLat G Qp LL O} (f : LatHom T₁.L T₂.L)
    (hfN : ∀ x ∈ W.N T₁, W.map f x ∈ W.N T₂) (π' : LetA O n) (c : ZMod n)

include hfN in
/- English proof (translation)
Rewrite `hx`, the goal using `[mem_NcS]`. Use `⟨hfN x hx.1, fun δ hδ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← W.map_γ, hx.2.1 δ hδ]`. Rewrite using `[← map_letA_smul, hx.2.2]`.
-/
theorem framepf_map_NcS (i : ZMod n) {x : W.DD T₁} (hx : x ∈ NcS W T₁ i) : W.map f x ∈ NcS W T₂ i := by
  rw [mem_NcS] at hx ⊢
  refine ⟨hfN x hx.1, fun δ hδ => ?_, ?_⟩
  · rw [← W.map_γ, hx.2.1 δ hδ]
  · rw [← map_letA_smul, hx.2.2]

include hfN in
/- English proof (translation)
Rewrite `hx`, the goal using `[mem_PiNS]`. Take `⟨⟨y, hy, hye⟩, hΔ⟩` from `hx`. Use `⟨⟨W.map f y, hfN y hy, ?_⟩, fun δ hδ => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_letA_smul, hye]`. Rewrite using `[← W.map_γ, hΔ δ hδ]`.
-/
theorem framepf_map_PiNS (k : ℕ) {x : W.DD T₁} (hx : x ∈ PiNS W T₁ π' k) :
    W.map f x ∈ PiNS W T₂ π' k := by
  rw [mem_PiNS] at hx ⊢
  obtain ⟨⟨y, hy, hye⟩, hΔ⟩ := hx
  refine ⟨⟨W.map f y, hfN y hy, ?_⟩, fun δ hδ => ?_⟩
  · rw [← map_letA_smul, hye]
  · rw [← W.map_γ, hΔ δ hδ]

include hfN in
/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨_, ⟨z, hz, rfl⟩, rfl⟩` from `hx`. Rewrite using `[W.map_φ]`. Conclude with `Submodule.subset_span ⟨_, ⟨W.map f z, hfN z hz, (map_letA_smul W T₁ f _ z).symm⟩, rfl⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul s x _ hx => rw [map_letA_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem framepf_map_φspan (i : ZMod n) {x : W.DD T₁} (hx : x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T₁ (W.Nl T₁ i)) :
    W.map f x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T₂ (W.Nl T₂ i) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hx
    rw [W.map_φ]
    exact Submodule.subset_span ⟨_, ⟨W.map f z, hfN z hz, (map_letA_smul W T₁ f _ z).symm⟩, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul s x _ hx => rw [map_letA_smul]; exact Submodule.smul_mem _ _ hx

include hfN in
/- English proof (translation)
Take `⟨⟨h1, h2⟩, h3⟩` from `hx`. Use `⟨⟨framepf_map_φspan f hfN (c - 1) h1, (mem_DelS W T₂ _).2 fun δ hδ => ?_⟩, (mem_letS W T₂ c _).2 ?_⟩` and prove the remaining obligations. Rewrite using `[← W.map_γ, (mem_DelS W T₁ x).1 h2 δ hδ]`. Rewrite using `[← map_letA_smul, (mem_letS W T₁ c x).1 h3]`.
-/
theorem framepf_map_PcS {x : W.DD T₁} (hx : x ∈ PcS W T₁ c) : W.map f x ∈ PcS W T₂ c := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hx
  refine ⟨⟨framepf_map_φspan f hfN (c - 1) h1, (mem_DelS W T₂ _).2 fun δ hδ => ?_⟩, (mem_letS W T₂ c _).2 ?_⟩
  · rw [← W.map_γ, (mem_DelS W T₁ x).1 h2 δ hδ]
  · rw [← map_letA_smul, (mem_letS W T₁ c x).1 h3]

include hfN in
/- English proof (translation)
Take `⟨p, hp, rfl⟩` from `hx`. Conclude with `⟨W.map f p, framepf_map_PcS f hfN c hp, (map_letA_smul W T₁ f _ p).symm⟩`.
-/
theorem framepf_map_JP (Eπ : LetA O n) (h' M : ℕ) {x : W.DD T₁} (hx : x ∈ JP W T₁ π' Eπ h' M c) :
    W.map f x ∈ JP W T₂ π' Eπ h' M c := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨W.map f p, framepf_map_PcS f hfN c hp, (map_letA_smul W T₁ f _ p).symm⟩

def framepf_Lmap : LcQ W T₁ π' c →ₗ[O] LcQ W T₂ π' c :=
  Submodule.mapQ _ _
    (((W.map f).restrictScalars O).restrict (p := NcS W T₁ (c - 1)) (q := NcS W T₂ (c - 1))
      fun _ hx => framepf_map_NcS f hfN (c - 1) hx)
    fun _ hx => framepf_map_PiNS f hfN π' 1 hx

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem framepf_Lmap_mkL (z : W.DD T₁) (h₁ : z ∈ NcS W T₁ (c - 1)) (h₂ : W.map f z ∈ NcS W T₂ (c - 1)) :
    framepf_Lmap f hfN π' c (mkL W T₁ π' c z h₁) = mkL W T₂ π' c (W.map f z) h₂ := rfl

/- English proof (translation)
Take `⟨m, e, y, h₁, h₂, rfl, rfl⟩` from `h`. Rewrite using `[map_sum]`. Both sides reduce to the same expression.
-/
theorem framepf_LAover {x₁ : LA W T₁ π' c} {x₂ : LA W T₂ π' c} (h : LAover W f π' c x₁ x₂) :
    x₂ = (framepf_Lmap f hfN π' c).lTensor W.EE x₁ := by
  obtain ⟨m, e, y, h₁, h₂, rfl, rfl⟩ := h
  rw [map_sum]
  rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul e ℓ => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem framepf_Lmap_smulLA (a : LetA O n) (x : LA W T₁ π' c) :
    (framepf_Lmap f hfN π' c).lTensor W.EE (smulLA W T₁ π' c a x) =
      smulLA W T₂ π' c a ((framepf_Lmap f hfN π' c).lTensor W.EE x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e ℓ => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Take `⟨t, rfl⟩` from `hx`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a s => exact ⟨a ⊗ₜ ⟨framepf_Lmap f hfN π' c s, trivial⟩, rfl⟩`. Consider the case `add x y hx hy => rw [map_add, map_add]`.

Conclude with `Submodule.add_mem _ hx hy`.
-/
theorem framepf_Lmap_toLA {x : LA W T₁ π' c} (hx : x ∈ LinearMap.range (toLA W T₁ π' c ⊤)) :
    (framepf_Lmap f hfN π' c).lTensor W.EE x ∈ LinearMap.range (toLA W T₂ π' c ⊤) := by
  obtain ⟨t, rfl⟩ := hx
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a s => exact ⟨a ⊗ₜ ⟨framepf_Lmap f hfN π' c s, trivial⟩, rfl⟩
  | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy

/- English proof (translation)
Use `show smulLA W T₂ π' c _ _ ∈ LinearMap.range (toLA W T₂ π' c ⊤)`. Rewrite using `[← framepf_Lmap_smulLA]`. Conclude with `framepf_Lmap_toLA f hfN π' c hx`.
-/
theorem framepf_Lmap_LamLA (Eπ : LetA O n) (h' : ℕ) {x : LA W T₁ π' c}
    (hx : x ∈ LamLA W T₁ π' Eπ h' c ⊤) :
    (framepf_Lmap f hfN π' c).lTensor W.EE x ∈ LamLA W T₂ π' Eπ h' c ⊤ := by
  show smulLA W T₂ π' c _ _ ∈ LinearMap.range (toLA W T₂ π' c ⊤)
  rw [← framepf_Lmap_smulLA]
  exact framepf_Lmap_toLA f hfN π' c hx

/- English proof (translation)
Take `⟨t, ht, rfl⟩` from `hx`. Rewrite using `[framepf_Lmap_smulLA]`. Conclude with `⟨_, framepf_Lmap_toLA f hfN π' c ht, rfl⟩`.
-/
theorem framepf_Lmap_JLA (Eπ : LetA O n) (h' M : ℕ) {x : LA W T₁ π' c}
    (hx : x ∈ JLA W T₁ π' Eπ h' M c) :
    (framepf_Lmap f hfN π' c).lTensor W.EE x ∈ JLA W T₂ π' Eπ h' M c := by
  obtain ⟨t, ht, rfl⟩ := hx
  rw [framepf_Lmap_smulLA]
  exact ⟨_, framepf_Lmap_toLA f hfN π' c ht, rfl⟩

/- English proof (translation)
Apply `hinj` to reduce the goal to its premises. Take `⟨⟨z, hz⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ ℓ`. Establish `h1` using `hm₂ _ (framepf_map_NcS f hfN (c - 1) hz)`. Establish `h2` using `framepf_map_PiNS f hfN π' 1 (hm₁ z hz)`. Establish `h3` using `Submodule.sub_mem _ h1 h2`.

Rewrite `h3` using `[map_sub, LinearMap.map_smul_of_tower, sub_sub_sub_cancel_right]`. Conclude with `h3`. Establish `h3` using `Submodule.sub_mem _ (hγ₂ (framepf_Lmap f hfN π' c ℓ)) (framepf_map_PiNS f hfN π' M (hγ₁ ℓ))`. Rewrite `h3` using `[map_sub, W.map_γ]`. Rewrite using `[map_sub]`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.
-/
theorem framepf_hh_nat (M : ℕ) (lσ : O)
    (hinj : ∀ x ∈ PiNS W T₂ π' 1, W.γD T₂ W.gam x - x ∈ PiNS W T₂ π' M → x ∈ PiNS W T₂ π' M)
    (hh₁ : LcQ W T₁ π' c →ₗ[O] W.DD T₁) (hh₂ : LcQ W T₂ π' c →ₗ[O] W.DD T₂)
    (hγ₁ : ∀ ℓ, W.γD T₁ W.gam (hh₁ ℓ) - hh₁ ℓ ∈ PiNS W T₁ π' M)
    (hγ₂ : ∀ ℓ, W.γD T₂ W.gam (hh₂ ℓ) - hh₂ ℓ ∈ PiNS W T₂ π' M)
    (hm₁ : ∀ z hz, hh₁ (mkL W T₁ π' c z hz) - lσ • z ∈ PiNS W T₁ π' 1)
    (hm₂ : ∀ z hz, hh₂ (mkL W T₂ π' c z hz) - lσ • z ∈ PiNS W T₂ π' 1) (ℓ : LcQ W T₁ π' c) :
    hh₂ (framepf_Lmap f hfN π' c ℓ) - W.map f (hh₁ ℓ) ∈ PiNS W T₂ π' M := by
  apply hinj
  · obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ ℓ
    have h1 := hm₂ _ (framepf_map_NcS f hfN (c - 1) hz)
    have h2 := framepf_map_PiNS f hfN π' 1 (hm₁ z hz)
    have h3 := Submodule.sub_mem _ h1 h2
    rw [map_sub, LinearMap.map_smul_of_tower, sub_sub_sub_cancel_right] at h3
    exact h3
  · have h3 := Submodule.sub_mem _ (hγ₂ (framepf_Lmap f hfN π' c ℓ)) (framepf_map_PiNS f hfN π' M (hγ₁ ℓ))
    rw [map_sub, W.map_γ] at h3
    rw [map_sub]
    convert h3 using 1
    abel

end Map

section One

variable {T : LocLat G Qp LL O} (π' : LetA O n) (c : ZMod n)

/- English proof (translation)
Establish `: smulLA W T π' c b t = algebraMap (LetA O n) W.EE b • t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul e ℓ => rfl`. Consider the case `add x y hx hy => rw [map_add, hx, hy, smul_add]`.

Rewrite using `[this, map_smul, algebraMap_smul]`.
-/
theorem framepf_Ψ_smulLA {T' : LocLat G Qp LL O} (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T')
    (b : LetA O n) (t : LA W T π' c) : Ψ (smulLA W T π' c b t) = b • Ψ t := by
  have : smulLA W T π' c b t = algebraMap (LetA O n) W.EE b • t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul e ℓ => rfl
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
  rw [this, map_smul, algebraMap_smul]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul e ℓ => rfl`. Consider the case `add x y hx hy => rw [map_add, hx, hy, smul_add]`.
-/
theorem framepf_smulLA_alg (b : LetA O n) (t : LA W T π' c) :
    smulLA W T π' c b t = algebraMap (LetA O n) W.EE b • t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul e ℓ => rfl
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, rfl⟩ k`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, W.AΔ.zero_mem, by simp⟩`. Consider the case `tmul a s`.

Use `⟨bL.repr s k • (a : LetA O n), W.AΔ.smul_mem a.2 _, ?_⟩` and prove the remaining obligations. Establish `: toLA W T π' c ⊤ (a ⊗ₜ s) = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T π' c)` using `rfl`. Rewrite using `[this, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, mul_smul_comm, Algebra.smul_def, map_mul (algebraMap (LetA O n) W.EE) (algebraMap O _ _), ← IsScalarTower.algebraMap_apply, mul_comm]`. Consider the case `add x y hx hy`. Take `⟨a, ha, hae⟩` from `hx`.

Take `⟨b, hb, hbe⟩` from `hy`. Use `⟨a + b, W.AΔ.add_mem ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, Finsupp.add_apply, hae, hbe, mul_add, map_add]`. Introduce `h choose a ha hae using h`. Use `⟨∑ k, (⟨a k, ha k⟩ : ↥W.AΔ) ⊗ₜ ⟨bL k, trivial⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sum]`. Use `conv_rhs => rw [← (Algebra.TensorProduct.basis W.EE bL).sum_repr x]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hae, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Both sides reduce to the same expression.
-/
theorem framepf_mem_toLA {r : ℕ} (bL : Module.Basis (Fin r) O (LcQ W T π' c)) (x : LA W T π' c) :
    x ∈ LinearMap.range (toLA W T π' c ⊤) ↔ ∀ k, ∃ a ∈ W.AΔ,
      (Algebra.TensorProduct.basis W.EE bL).repr x k =
        algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) := by
  constructor
  · rintro ⟨t, rfl⟩ k
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, W.AΔ.zero_mem, by simp⟩
    | tmul a s =>
      refine ⟨bL.repr s k • (a : LetA O n), W.AΔ.smul_mem a.2 _, ?_⟩
      have : toLA W T π' c ⊤ (a ⊗ₜ s) =
        algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T π' c) := rfl
      rw [this, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, mul_smul_comm, Algebra.smul_def, map_mul (algebraMap (LetA O n) W.EE) (algebraMap O _ _),
        ← IsScalarTower.algebraMap_apply, mul_comm]
    | add x y hx hy =>
      obtain ⟨a, ha, hae⟩ := hx
      obtain ⟨b, hb, hbe⟩ := hy
      refine ⟨a + b, W.AΔ.add_mem ha hb, ?_⟩
      rw [map_add, map_add, Finsupp.add_apply, hae, hbe, mul_add, map_add]
  · intro h
    choose a ha hae using h
    refine ⟨∑ k, (⟨a k, ha k⟩ : ↥W.AΔ) ⊗ₜ ⟨bL k, trivial⟩, ?_⟩
    rw [map_sum]
    conv_rhs => rw [← (Algebra.TensorProduct.basis W.EE bL).sum_repr x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hae, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl

/- English proof (translation)
Set `bL : Module.Basis (Fin r) O (LcQ W T π' c)` to `Module.Basis.ofEquivFun eL`. Use `set β := Algebra.TensorProduct.basis W.EE bL with hβ`. Establish `hA : ∀ a : LetA O n, ((PD.p : ℕ) : LetA O n) ^ j * a = 0 → a = 0`. Establish `h1 : ∀ a : LetA O n, ((PD.p : ℕ) : LetA O n) * a = 0 → a = 0`. Introduce `a ha`.

Use function extensionality and compare the values at `i`. Use extensionality with `d`. Use `congrArg (PowerSeries.coeff d) (congrFun ha i)` as an intermediate fact. Rewrite `this` using `[Pi.mul_apply, Pi.natCast_apply, ← map_natCast (PowerSeries.C (R := O)), PowerSeries.coeff_C_mul]`. Conclude with `hℓ _ this`.

Use `clear hj`. Proceed by induction on `j with`. Consider the case `zero => intro a ha`. Simplify using `using ha`. Consider the case `succ j ih => intro a ha; exact h1 a (ih _ (by rw [← ha]; ring))`.

Take `⟨t, ht, hte⟩` from `hj`. Establish `hxc` using `(framepf_mem_toLA π' c bL _).1 hx`. Establish `htc` using `(framepf_mem_toLA π' c bL _).1 ht`. Establish `hg : IsUnit (algebraMap (LetA O n) W.EE (π' ^ M * Eπ ^ (3 * h')))`. Rewrite using `[map_mul, map_pow, map_pow]`.

Conclude with `(hu.pow _).mul (huE.pow _)`. Establish `hΛ : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h'))`. Rewrite using `[map_pow]`. Conclude with `huE.pow _`. Take `⟨g, hge⟩` from `hg`.

Take `⟨Λ, hΛe⟩` from `hΛ`. Use `⟨((g⁻¹ : W.EEˣ) : W.EE) • x, (framepf_mem_toLA π' c bL _).2 fun k => ?_, ?_⟩` and prove the remaining obligations. Take `⟨a, ha, hae⟩` from `hxc k`. Take `⟨b, hb, hbe⟩` from `htc k`. Rewrite `hae` using `[framepf_smulLA_alg, map_smul, Finsupp.smul_apply, smul_eq_mul, ← hΛe, ← hβ]`.

Rewrite `hbe` using `[← hβ]`. Establish `h1 : (g : W.EE) * β.repr t k = ((PD.p : ℕ) : W.EE) ^ j * β.repr x k`. Use `congrArg (fun z => β.repr z k) hte` as an intermediate fact. Rewrite `this` using `[framepf_smulLA_alg, map_smul, Finsupp.smul_apply, smul_eq_mul, ← hge, ← algebraMap_smul W.EE, map_smul, Finsupp.smul_apply, smul_eq_mul, map_pow, map_natCast]`. Conclude with `this`.

Take `⟨b', hb'⟩` from `W.EE_sat ((letE c : LetA O n) * b) j (by`. Rewrite using `[← hbe, Ideal.mem_span_singleton]`. Use `⟨((g⁻¹ : W.EEˣ) : W.EE) * β.repr x k, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_left_comm, ← h1, Units.inv_mul_cancel_left])`. Establish `hb'Δ : b' ∈ W.AΔ`.

Introduce `δ hδ`. Rewrite using `[← sub_eq_zero]`. Apply `hA` to reduce the goal to its premises. Establish `h2` using `congrArg (W.γA δ) hb'`. Rewrite `h2` using `[map_mul, map_mul, map_pow, map_natCast, hb δ hδ, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]`.

Rewrite using `[mul_sub, ← h2, hb', sub_self]`. Use `⟨b', hb'Δ, ?_⟩` and prove the remaining obligations. Establish `h3 : ((PD.p : ℕ) : LetA O n) ^ j * ((letE c : LetA O n) * a - Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h')) * ((letE c : LetA O n) * b')) = 0`. Apply `W.EE_inj` to reduce the goal to its premises. Establish `h4 : ((PD.p : ℕ) : LetA O n) ^ j * ((letE c : LetA O n) * b') = (letE c : LetA O n) * b`.

Rewrite using `[mul_left_comm, ← hb', ← mul_assoc, Formalism.MainNotions.LiftingTheory.wmap_letE_idem]`. Rewrite using `[mul_sub, mul_left_comm _ (Eπ ^ h' * _), h4, map_sub, map_mul, ← hae, map_mul (algebraMap (LetA O n) W.EE) (Eπ ^ h' * _), map_mul (algebraMap (LetA O n) W.EE) (Eπ ^ h'), ← hbe, ← hge, ← hΛe, map_pow, map_natCast, map_zero, mul_assoc, h1]`. Expand and normalize the polynomial expressions, which then agree. Establish `h5` using `congrArg (algebraMap (LetA O n) W.EE) (sub_eq_zero.1 (hA _ h3))`. Rewrite `h5` using `[← hae, map_mul (algebraMap (LetA O n) W.EE) (Eπ ^ h' * _), map_mul (algebraMap (LetA O n) W.EE) (Eπ ^ h'), ← hge, ← hΛe, mul_assoc, Units.mul_right_inj]`.

Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul, ← hβ, h5, Units.inv_mul_cancel_left]`. Rewrite using `[framepf_smulLA_alg, ← hge, smul_smul, Units.mul_inv, one_smul]`.
-/
theorem framepf_JLA_sat {r : ℕ} (eL : LcQ W T π' c ≃ₗ[O] (Fin r → O)) (Eπ : LetA O n) (h' M : ℕ)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π')) (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ))
    (hℓ : ∀ o : O, ((PD.p : ℕ) : O) * o = 0 → o = 0) (j : ℕ) (x : LA W T π' c)
    (hx : x ∈ LamLA W T π' Eπ h' c ⊤) (hj : ((PD.p : ℕ) : O) ^ j • x ∈ JLA W T π' Eπ h' M c) :
    x ∈ JLA W T π' Eπ h' M c := by
  let bL : Module.Basis (Fin r) O (LcQ W T π' c) := Module.Basis.ofEquivFun eL
  set β := Algebra.TensorProduct.basis W.EE bL with hβ
  have hA : ∀ a : LetA O n, ((PD.p : ℕ) : LetA O n) ^ j * a = 0 → a = 0 := by
    have h1 : ∀ a : LetA O n, ((PD.p : ℕ) : LetA O n) * a = 0 → a = 0 := by
      intro a ha
      funext i
      ext d
      have := congrArg (PowerSeries.coeff d) (congrFun ha i)
      rw [Pi.mul_apply, Pi.natCast_apply, ← map_natCast (PowerSeries.C (R := O)),
        PowerSeries.coeff_C_mul] at this
      exact hℓ _ this
    clear hj
    induction j with
    | zero => intro a ha; simpa using ha
    | succ j ih => intro a ha; exact h1 a (ih _ (by rw [← ha]; ring))
  obtain ⟨t, ht, hte⟩ := hj
  have hxc := (framepf_mem_toLA π' c bL _).1 hx
  have htc := (framepf_mem_toLA π' c bL _).1 ht
  have hg : IsUnit (algebraMap (LetA O n) W.EE (π' ^ M * Eπ ^ (3 * h'))) := by
    rw [map_mul, map_pow, map_pow]
    exact (hu.pow _).mul (huE.pow _)
  have hΛ : IsUnit (algebraMap (LetA O n) W.EE (Eπ ^ h')) := by
    rw [map_pow]
    exact huE.pow _
  obtain ⟨g, hge⟩ := hg
  obtain ⟨Λ, hΛe⟩ := hΛ
  refine ⟨((g⁻¹ : W.EEˣ) : W.EE) • x, (framepf_mem_toLA π' c bL _).2 fun k => ?_, ?_⟩
  · obtain ⟨a, ha, hae⟩ := hxc k
    obtain ⟨b, hb, hbe⟩ := htc k
    rw [framepf_smulLA_alg, map_smul, Finsupp.smul_apply, smul_eq_mul, ← hΛe, ← hβ] at hae
    rw [← hβ] at hbe
    have h1 : (g : W.EE) * β.repr t k = ((PD.p : ℕ) : W.EE) ^ j * β.repr x k := by
      have := congrArg (fun z => β.repr z k) hte
      rw [framepf_smulLA_alg, map_smul, Finsupp.smul_apply, smul_eq_mul, ← hge,
        ← algebraMap_smul W.EE, map_smul, Finsupp.smul_apply, smul_eq_mul, map_pow, map_natCast] at this
      exact this
    obtain ⟨b', hb'⟩ := W.EE_sat ((letE c : LetA O n) * b) j (by
      rw [← hbe, Ideal.mem_span_singleton]
      refine ⟨((g⁻¹ : W.EEˣ) : W.EE) * β.repr x k, ?_⟩
      rw [mul_left_comm, ← h1, Units.inv_mul_cancel_left])
    have hb'Δ : b' ∈ W.AΔ := by
      intro δ hδ
      rw [← sub_eq_zero]
      apply hA
      have h2 := congrArg (W.γA δ) hb'
      rw [map_mul, map_mul, map_pow, map_natCast, hb δ hδ, Formalism.MainNotions.LiftingTheory.wmap_γA_letE] at h2
      rw [mul_sub, ← h2, hb', sub_self]
    refine ⟨b', hb'Δ, ?_⟩
    have h3 : ((PD.p : ℕ) : LetA O n) ^ j *
        ((letE c : LetA O n) * a - Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h')) * ((letE c : LetA O n) * b')) = 0 := by
      apply W.EE_inj
      have h4 : ((PD.p : ℕ) : LetA O n) ^ j * ((letE c : LetA O n) * b') = (letE c : LetA O n) * b := by
        rw [mul_left_comm, ← hb', ← mul_assoc, Formalism.MainNotions.LiftingTheory.wmap_letE_idem]
      rw [mul_sub, mul_left_comm _ (Eπ ^ h' * _), h4, map_sub, map_mul, ← hae,
        map_mul (algebraMap (LetA O n) W.EE) (Eπ ^ h' * _), map_mul (algebraMap (LetA O n) W.EE) (Eπ ^ h'),
        ← hbe, ← hge, ← hΛe, map_pow, map_natCast, map_zero, mul_assoc, h1]
      ring
    have h5 := congrArg (algebraMap (LetA O n) W.EE) (sub_eq_zero.1 (hA _ h3))
    rw [← hae, map_mul (algebraMap (LetA O n) W.EE) (Eπ ^ h' * _),
      map_mul (algebraMap (LetA O n) W.EE) (Eπ ^ h'), ← hge, ← hΛe, mul_assoc, Units.mul_right_inj] at h5
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← hβ, h5, Units.inv_mul_cancel_left]
  · rw [framepf_smulLA_alg, ← hge, smul_smul, Units.mul_inv, one_smul]

end One

section Nat

variable {T₁ T₂ : LocLat G Qp LL O} (f : LatHom T₁.L T₂.L)
    (hfN : ∀ x ∈ W.N T₁, W.map f x ∈ W.N T₂) (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n)

/- English proof (translation)
Take `⟨t, ht⟩` from `hx`. Establish `key : ∀ t : ↥W.AΔ ⊗[O] ↥(⊤ : Submodule O (LcQ W T₁ π' c)), ∃ p ∈ PcS W T₂ c, Ψ₂ ((framepf_Lmap f hfN π' c).lTensor W.EE (toLA W T₁ π' c ⊤ t)) - W.map f (Ψ₁ (toLA W T₁ π' c ⊤ t)) = (π' ^ M * Eπ ^ (4 * h')) • p`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, by simp⟩`.

Consider the case `tmul a s`. Establish `e : toLA W T₁ π' c ⊤ (a ⊗ₜ s) = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T₁ π' c)` using `rfl`. Take `⟨⟨d, hd, hde⟩, hΔ⟩` from `(mem_PiNS W T₂ π' M _).1 (hnat s)`. Establish `hdΔ` using `invLiftPf_quot_Δ W T₂ π' hu hΔπ M d hd (by rw [hde]; exact hΔ)`. Use `⟨((letE c : LetA O n) * a * u) • W.φD T₂ d, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `show _ ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T₂ (W.Nl T₂ (c - 1))`. Rewrite using `[mul_assoc, mul_comm, mul_smul, ← φD_letE]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨d, hd, rfl⟩, rfl⟩)`. Use `show _ ∈ DelS W T₂`. Rewrite using `[mem_DelS]`.

Introduce `δ hδ`. Rewrite using `[gradNPf_γD_smul, ← W.φγ_comm, hdΔ.2 δ hδ, map_mul, map_mul, huΔ δ hδ, a.2 δ hδ, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]`. Use `show _ ∈ letS W T₂ c`. Rewrite using `[mem_letS, smul_smul, ← mul_assoc, ← mul_assoc, Formalism.MainNotions.LiftingTheory.wmap_letE_idem]`. Rewrite using `[e, LinearMap.lTensor_tmul, hΨ₂, hΨ₁, map_smul, W.map_φ, ← smul_sub, ← map_sub, ← hde, Formalism.MainNotions.LiftingTheory.wmap_φD_smul, map_pow, hφ, algebraMap_smul, smul_smul, smul_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add x y hx hy`. Take `⟨p, hp, hpe⟩` from `hx`. Take `⟨q, hq, hqe⟩` from `hy`.

Use `⟨p + q, Submodule.add_mem _ hp hq, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, ← hpe, ← hqe]`. Simplify using `only [map_add]`. Normalize the expressions using the abelian group laws. Take `⟨p, hp, hpe⟩` from `key t`.

Use `⟨p, hp, ?_⟩` and prove the remaining obligations. Use `show (π' ^ M * Eπ ^ (3 * h')) • p = _`. Rewrite using `[← sub_eq_zero]`. Apply `gradNPf_tf W T₂ (Eπ ^ h') (by rw [map_pow]; exact huE.pow _)` to reduce the goal to its premises. Rewrite `hpe` using `[ht, framepf_Lmap_smulLA, framepf_Ψ_smulLA, framepf_Ψ_smulLA, map_letA_smul, ← smul_sub]`.

Rewrite using `[smul_sub, hpe, smul_smul, ← sub_smul, show Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h')) - π' ^ M * Eπ ^ (4 * h') = 0 by ring, zero_smul]`.
-/
theorem framepf_Ψα_nat (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (u : LetA O n) (huΔ : u ∈ W.AΔ) (hφ : W.φA π' ^ M = π' ^ M * Eπ ^ (4 * h') * u)
    (hh₁ : LcQ W T₁ π' c →ₗ[O] W.DD T₁) (hh₂ : LcQ W T₂ π' c →ₗ[O] W.DD T₂)
    (hnat : ∀ ℓ, hh₂ (framepf_Lmap f hfN π' c ℓ) - W.map f (hh₁ ℓ) ∈ PiNS W T₂ π' M)
    (Ψ₁ : W.EE ⊗[O] LcQ W T₁ π' c →ₗ[W.EE] W.DD T₁) (hΨ₁ : ∀ e ℓ, Ψ₁ (e ⊗ₜ ℓ) = e • W.φD T₁ (hh₁ ℓ))
    (Ψ₂ : W.EE ⊗[O] LcQ W T₂ π' c →ₗ[W.EE] W.DD T₂) (hΨ₂ : ∀ e ℓ, Ψ₂ (e ⊗ₜ ℓ) = e • W.φD T₂ (hh₂ ℓ))
    (x : LA W T₁ π' c) (hx : x ∈ LamLA W T₁ π' Eπ h' c ⊤) :
    Ψ₂ ((framepf_Lmap f hfN π' c).lTensor W.EE x) - W.map f (Ψ₁ x) ∈ JP W T₂ π' Eπ h' M c := by
  obtain ⟨t, ht⟩ := hx
  have key : ∀ t : ↥W.AΔ ⊗[O] ↥(⊤ : Submodule O (LcQ W T₁ π' c)), ∃ p ∈ PcS W T₂ c,
      Ψ₂ ((framepf_Lmap f hfN π' c).lTensor W.EE (toLA W T₁ π' c ⊤ t)) - W.map f (Ψ₁ (toLA W T₁ π' c ⊤ t)) =
        (π' ^ M * Eπ ^ (4 * h')) • p := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | tmul a s =>
      have e : toLA W T₁ π' c ⊤ (a ⊗ₜ s) =
        algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T₁ π' c) := rfl
      obtain ⟨⟨d, hd, hde⟩, hΔ⟩ := (mem_PiNS W T₂ π' M _).1 (hnat s)
      have hdΔ := invLiftPf_quot_Δ W T₂ π' hu hΔπ M d hd (by rw [hde]; exact hΔ)
      refine ⟨((letE c : LetA O n) * a * u) • W.φD T₂ d, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · show _ ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T₂ (W.Nl T₂ (c - 1))
        rw [mul_assoc, mul_comm, mul_smul, ← φD_letE]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨d, hd, rfl⟩, rfl⟩)
      · show _ ∈ DelS W T₂
        rw [mem_DelS]
        intro δ hδ
        rw [gradNPf_γD_smul, ← W.φγ_comm, hdΔ.2 δ hδ, map_mul, map_mul, huΔ δ hδ, a.2 δ hδ,
          Formalism.MainNotions.LiftingTheory.wmap_γA_letE]
      · show _ ∈ letS W T₂ c
        rw [mem_letS, smul_smul, ← mul_assoc, ← mul_assoc, Formalism.MainNotions.LiftingTheory.wmap_letE_idem]
      · rw [e, LinearMap.lTensor_tmul, hΨ₂, hΨ₁, map_smul, W.map_φ, ← smul_sub, ← map_sub, ← hde,
          Formalism.MainNotions.LiftingTheory.wmap_φD_smul, map_pow, hφ, algebraMap_smul, smul_smul, smul_smul]
        congr 1
        ring
    | add x y hx hy =>
      obtain ⟨p, hp, hpe⟩ := hx
      obtain ⟨q, hq, hqe⟩ := hy
      refine ⟨p + q, Submodule.add_mem _ hp hq, ?_⟩
      rw [smul_add, ← hpe, ← hqe]
      simp only [map_add]
      abel
  obtain ⟨p, hp, hpe⟩ := key t
  refine ⟨p, hp, ?_⟩
  show (π' ^ M * Eπ ^ (3 * h')) • p = _
  rw [← sub_eq_zero]
  apply gradNPf_tf W T₂ (Eπ ^ h') (by rw [map_pow]; exact huE.pow _)
  rw [ht, framepf_Lmap_smulLA, framepf_Ψ_smulLA, framepf_Ψ_smulLA, map_letA_smul, ← smul_sub] at hpe
  rw [smul_sub, hpe, smul_smul, ← sub_smul, show Eπ ^ h' * (π' ^ M * Eπ ^ (3 * h')) -
    π' ^ M * Eπ ^ (4 * h') = 0 by ring, zero_smul]

variable (Ψ₁ : W.EE ⊗[O] LcQ W T₁ π' c →ₗ[W.EE] W.DD T₁) (Ψ₂ : W.EE ⊗[O] LcQ W T₂ π' c →ₗ[W.EE] W.DD T₂)
    (hnat : ∀ x ∈ LamLA W T₁ π' Eπ h' c ⊤,
      Ψ₂ ((framepf_Lmap f hfN π' c).lTensor W.EE x) - W.map f (Ψ₁ x) ∈ JP W T₂ π' Eπ h' M c)

include hnat in

/- English proof (translation)
Establish `h` using `Submodule.add_mem _ (hnat x₁ hx₁) (framepf_map_JP f hfN π' c Eπ h' M hxy)`. Rewrite `h` using `[map_sub, sub_add_sub_cancel]`. Rewrite using `[framepf_LAover f hfN π' c hov]`. Conclude with `h`.
-/
theorem framepf_α_nat (x₁ : LA W T₁ π' c) (hx₁ : x₁ ∈ LamLA W T₁ π' Eπ h' c ⊤) (x₂ : LA W T₂ π' c)
    (y₁ : W.DD T₁) (hov : LAover W f π' c x₁ x₂) (hxy : Ψ₁ x₁ - y₁ ∈ JP W T₁ π' Eπ h' M c) :
    Ψ₂ x₂ - W.map f y₁ ∈ JP W T₂ π' Eπ h' M c := by
  have h := Submodule.add_mem _ (hnat x₁ hx₁) (framepf_map_JP f hfN π' c Eπ h' M hxy)
  rw [map_sub, sub_add_sub_cancel] at h
  rw [framepf_LAover f hfN π' c hov]
  exact h

include hnat in

/- English proof (translation)
Establish `hL` using `framepf_Lmap_LamLA f hfN π' c Eπ h' (hΦ₁ y₁ hy₁)`. Establish `h1` using `hJ₂ _ (Submodule.add_mem _ (hnat _ (hΦ₁ y₁ hy₁)) (framepf_map_JP f hfN π' c Eπ h' M (hαβ y₁ hy₁)))`. Establish `h2` using `Submodule.sub_mem _ (hβα _ hL) h1`. Rewrite `h2` using `[map_sub (W.map f), sub_add_sub_cancel, map_sub Φ₂, sub_sub_sub_cancel_left, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, ← smul_sub]`. Establish `h3` using `hsat _ (Submodule.sub_mem _ (hΦ₂ _ hy₂) hL) h2`.

Establish `h4` using `Submodule.add_mem _ h3 (framepf_Lmap_JLA f hfN π' c Eπ h' M hxy)`. Rewrite `h4` using `[map_sub, sub_add_sub_cancel]`. Rewrite using `[framepf_LAover f hfN π' c hov]`. Conclude with `h4`.
-/
theorem framepf_β_nat (Φ₁ : W.DD T₁ →ₗ[W.EE] W.EE ⊗[O] LcQ W T₁ π' c)
    (Φ₂ : W.DD T₂ →ₗ[W.EE] W.EE ⊗[O] LcQ W T₂ π' c) (lam : O)
    (hΦ₁ : ∀ y ∈ LamPS W T₁ Eπ h' c, Φ₁ y ∈ LamLA W T₁ π' Eπ h' c ⊤)
    (hΦ₂ : ∀ y ∈ LamPS W T₂ Eπ h' c, Φ₂ y ∈ LamLA W T₂ π' Eπ h' c ⊤)
    (hJ₂ : ∀ y ∈ JP W T₂ π' Eπ h' M c, Φ₂ y ∈ JLA W T₂ π' Eπ h' M c)
    (hαβ : ∀ y ∈ LamPS W T₁ Eπ h' c, Ψ₁ (Φ₁ y) - lam • y ∈ JP W T₁ π' Eπ h' M c)
    (hβα : ∀ x ∈ LamLA W T₂ π' Eπ h' c ⊤, Φ₂ (Ψ₂ x) - lam • x ∈ JLA W T₂ π' Eπ h' M c)
    (hsat : ∀ x ∈ LamLA W T₂ π' Eπ h' c ⊤, lam • x ∈ JLA W T₂ π' Eπ h' M c → x ∈ JLA W T₂ π' Eπ h' M c)
    (y₁ : W.DD T₁) (hy₁ : y₁ ∈ LamPS W T₁ Eπ h' c) (hy₂ : W.map f y₁ ∈ LamPS W T₂ Eπ h' c)
    (x₁ : LA W T₁ π' c) (x₂ : LA W T₂ π' c) (hov : LAover W f π' c x₁ x₂)
    (hxy : Φ₁ y₁ - x₁ ∈ JLA W T₁ π' Eπ h' M c) :
    Φ₂ (W.map f y₁) - x₂ ∈ JLA W T₂ π' Eπ h' M c := by
  have hL := framepf_Lmap_LamLA f hfN π' c Eπ h' (hΦ₁ y₁ hy₁)
  have h1 := hJ₂ _ (Submodule.add_mem _ (hnat _ (hΦ₁ y₁ hy₁))
    (framepf_map_JP f hfN π' c Eπ h' M (hαβ y₁ hy₁)))
  have h2 := Submodule.sub_mem _ (hβα _ hL) h1
  rw [map_sub (W.map f), sub_add_sub_cancel, map_sub Φ₂, sub_sub_sub_cancel_left,
    LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, ← smul_sub] at h2
  have h3 := hsat _ (Submodule.sub_mem _ (hΦ₂ _ hy₂) hL) h2
  have h4 := Submodule.add_mem _ h3 (framepf_Lmap_JLA f hfN π' c Eπ h' M hxy)
  rw [map_sub, sub_add_sub_cancel] at h4
  rw [framepf_LAover f hfN π' c hov]
  exact h4

end Nat

end Local

end Formalism.MainNotions.N.Ln34

end
