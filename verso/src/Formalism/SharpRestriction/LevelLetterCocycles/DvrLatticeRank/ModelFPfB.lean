import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfA
import Formalism.SharpRestriction.LevelLetterCocycles.MapCompZero

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Mod

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)
    (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toLA_tmul (S : Submodule O (LcQ W T π' c)) (a : ↥W.AΔ) (s : ↥S) :
    toLA W T π' c S (a ⊗ₜ s) =
      algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T π' c) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smulLA_tmul (a : LetA O n) (e : W.EE) (z : LcQ W T π' c) :
    smulLA W T π' c a (e ⊗ₜ z) = (algebraMap (LetA O n) W.EE a * e) ⊗ₜ z := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem γLA_tmul (e : W.EE) (z : LcQ W T π' c) :
    γLA W T π' c (e ⊗ₜ z) = W.γE W.gamK e ⊗ₜ z := rfl

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul e z => rw [smulLA_tmul, smulLA_tmul, smulLA_tmul, ← mul_assoc, ← map_mul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem smulLA_smulLA (a b : LetA O n) (x : LA W T π' c) :
    smulLA W T π' c a (smulLA W T π' c b x) = smulLA W T π' c (a * b) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul e z => rw [smulLA_tmul, smulLA_tmul, smulLA_tmul, ← mul_assoc, ← map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul e z`. Rewrite using `[smulLA_tmul, γLA_tmul, γLA_tmul, smulLA_tmul, map_mul, W.γE_ext]`. Both sides reduce to the same expression.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem γLA_smulLA (a : LetA O n) (x : LA W T π' c) :
    γLA W T π' c (smulLA W T π' c a x) = smulLA W T π' c (W.γA W.gamK a) (γLA W T π' c x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul e z =>
    rw [smulLA_tmul, γLA_tmul, γLA_tmul, smulLA_tmul, map_mul, W.γE_ext]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show W.γ₀ g (W.γ₀ h (a i)) = W.γ₀ h (W.γ₀ g (a i))`. Rewrite using `[← AlgHom.mul_apply, ← map_mul, mul_comm g h, map_mul, AlgHom.mul_apply]`.
-/
theorem γA_comm (g h : W.Gam) (a : LetA O n) : W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
  funext i
  show W.γ₀ g (W.γ₀ h (a i)) = W.γ₀ h (W.γ₀ g (a i))
  rw [← AlgHom.mul_apply, ← map_mul, mul_comm g h, map_mul, AlgHom.mul_apply]

/- English proof (translation)
Introduce `δ hδ`. Rewrite using `[γA_comm, ha δ hδ]`.
-/
theorem γA_mem_AΔ (g : W.Gam) {a : LetA O n} (ha : a ∈ W.AΔ) : W.γA g a ∈ W.AΔ := by
  intro δ hδ
  rw [γA_comm, ha δ hδ]

/- English proof (translation)
Take `⟨t, rfl⟩` from `hu`. Establish `ht : t ∈ Submodule.span O {t : ↥W.AΔ ⊗[O] ↥(⊤ : Submodule O (LcQ W T π' c)) | ∃ a s, a ⊗ₜ s = t}`. Rewrite using `[TensorProduct.span_tmul_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨m, f, g, hfg⟩` from `Submodule.mem_span_set'.1 ht`.

Use `choose a s hs using fun j => (g j).2`. Use `choose x hx using fun j => Submodule.Quotient.mk_surjective _ ((s j : ↥(⊤ : Submodule O (LcQ W T π' c))) : LcQ W T π' c)`. Use `⟨m, fun j => f j • a j, fun j => (x j : W.DD T), fun j => (x j).2, ?_⟩` and prove the remaining obligations. Rewrite using `[← hfg, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[← hs j, TensorProduct.smul_tmul', toLA_tmul]`. Use `congr 1`. Conclude with `(hx j).symm`.
-/
theorem range_rep (u : LA W T π' c) (hu : u ∈ LinearMap.range (toLA W T π' c ⊤)) :
    ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T) (hy : ∀ j, y j ∈ NcS W T (c - 1)),
      u = ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ
        mkL W T π' c (y j) (hy j) := by
  classical
  obtain ⟨t, rfl⟩ := hu
  have ht : t ∈ Submodule.span O
      {t : ↥W.AΔ ⊗[O] ↥(⊤ : Submodule O (LcQ W T π' c)) | ∃ a s, a ⊗ₜ s = t} := by
    rw [TensorProduct.span_tmul_eq_top]
    trivial
  obtain ⟨m, f, g, hfg⟩ := Submodule.mem_span_set'.1 ht
  choose a s hs using fun j => (g j).2
  choose x hx using fun j =>
    Submodule.Quotient.mk_surjective _ ((s j : ↥(⊤ : Submodule O (LcQ W T π' c))) : LcQ W T π' c)
  refine ⟨m, fun j => f j • a j, fun j => (x j : W.DD T), fun j => (x j).2, ?_⟩
  rw [← hfg, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hs j, TensorProduct.smul_tmul', toLA_tmul]
  congr 1
  exact (hx j).symm

/- English proof (translation)
The claim follows from `Submodule.sum_mem _ fun j _ => ⟨(⟨a j, ha j⟩ : ↥W.AΔ) ⊗ₜ (⟨mkL W T π' c (y j) (hy j), trivial⟩ : ↥(⊤ : Submodule O _)), rfl⟩`.
-/
theorem rep_mem {m : ℕ} (a : Fin m → LetA O n) (ha : ∀ j, a j ∈ W.AΔ) (y : Fin m → W.DD T)
    (hy : ∀ j, y j ∈ NcS W T (c - 1)) :
    ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ mkL W T π' c (y j) (hy j) ∈
      LinearMap.range (toLA W T π' c ⊤) :=
  Submodule.sum_mem _ fun j _ =>
    ⟨(⟨a j, ha j⟩ : ↥W.AΔ) ⊗ₜ (⟨mkL W T π' c (y j) (hy j), trivial⟩ : ↥(⊤ : Submodule O _)), rfl⟩

/- English proof (translation)
Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smulLA_tmul, ← map_mul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem smulLA_rep (b : LetA O n) {m : ℕ} (a : Fin m → LetA O n) (z : Fin m → LcQ W T π' c) :
    smulLA W T π' c b (∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ z j) =
      ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * (b * a j)) ⊗ₜ z j := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smulLA_tmul, ← map_mul]
  congr 2
  ring

/- English proof (translation)
Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[γLA_tmul, W.γE_ext]`. Use `congr 2`. Use `show W.γA W.gamK ((letE c : LetA O n) * a j) = _`.

Rewrite using `[map_mul, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]`.
-/
theorem γLA_rep {m : ℕ} (a : Fin m → LetA O n) (z : Fin m → LcQ W T π' c) :
    γLA W T π' c (∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ z j) =
      ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * W.γA W.gamK (a j)) ⊗ₜ z j := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [γLA_tmul, W.γE_ext]
  congr 2
  show W.γA W.gamK ((letE c : LetA O n) * a j) = _
  rw [map_mul, Formalism.MainNotions.LiftingTheory.wmap_γA_letE]

/- English proof (translation)
Take `⟨m, a, y, hy, rfl⟩` from `range_rep W T π' c u hu`. Rewrite using `[smulLA_rep]`. Conclude with `rep_mem W T π' c _ (fun j => W.AΔ.mul_mem hb (a j).2) y hy`.
-/
theorem range_smul {b : LetA O n} (hb : b ∈ W.AΔ) {u : LA W T π' c}
    (hu : u ∈ LinearMap.range (toLA W T π' c ⊤)) :
    smulLA W T π' c b u ∈ LinearMap.range (toLA W T π' c ⊤) := by
  obtain ⟨m, a, y, hy, rfl⟩ := range_rep W T π' c u hu
  rw [smulLA_rep]
  exact rep_mem W T π' c _ (fun j => W.AΔ.mul_mem hb (a j).2) y hy

/- English proof (translation)
Take `⟨m, a, y, hy, rfl⟩` from `range_rep W T π' c u hu`. Rewrite using `[γLA_rep]`. Conclude with `rep_mem W T π' c _ (fun j => γA_mem_AΔ W _ (a j).2) y hy`.
-/
theorem range_γ {u : LA W T π' c} (hu : u ∈ LinearMap.range (toLA W T π' c ⊤)) :
    γLA W T π' c u ∈ LinearMap.range (toLA W T π' c ⊤) := by
  obtain ⟨m, a, y, hy, rfl⟩ := range_rep W T π' c u hu
  rw [γLA_rep]
  exact rep_mem W T π' c _ (fun j => γA_mem_AΔ W _ (a j).2) y hy

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_LamLA (x : LA W T π' c) :
    x ∈ LamLA W T π' Eπ h' c ⊤ ↔
      smulLA W T π' c (Eπ ^ h') x ∈ LinearMap.range (toLA W T π' c ⊤) := Iff.rfl

/- English proof (translation)
Rewrite using `[mem_LamLA, smulLA_smulLA, mul_comm, ← smulLA_smulLA]`. Conclude with `range_smul W T π' c ha hx`.
-/
theorem LamLA_smul {a : LetA O n} (ha : a ∈ W.AΔ) {x : LA W T π' c}
    (hx : x ∈ LamLA W T π' Eπ h' c ⊤) : smulLA W T π' c a x ∈ LamLA W T π' Eπ h' c ⊤ := by
  rw [mem_LamLA, smulLA_smulLA, mul_comm, ← smulLA_smulLA]
  exact range_smul W T π' c ha hx

/- English proof (translation)
Rewrite using `[mem_LamLA]`. Establish `h1 : Eπ ^ h' = u' ^ h' * W.γA W.gamK (Eπ ^ h')`. Rewrite using `[map_pow, hγE, mul_pow, ← mul_assoc, ← mul_pow, huu, one_pow, one_mul]`. Rewrite using `[h1, ← smulLA_smulLA, ← γLA_smulLA]`. Conclude with `range_smul W T π' c (W.AΔ.pow_mem hu' h') (range_γ W T π' c hx)`.
-/
theorem LamLA_γ {u u' : LetA O n} (hu' : u' ∈ W.AΔ) (huu : u' * u = 1)
    (hγE : W.γA W.gamK Eπ = u * Eπ) {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤) :
    γLA W T π' c x ∈ LamLA W T π' Eπ h' c ⊤ := by
  rw [mem_LamLA]
  have h1 : Eπ ^ h' = u' ^ h' * W.γA W.gamK (Eπ ^ h') := by
    rw [map_pow, hγE, mul_pow, ← mul_assoc, ← mul_pow, huu, one_pow, one_mul]
  rw [h1, ← smulLA_smulLA, ← γLA_smulLA]
  exact range_smul W T π' c (W.AΔ.pow_mem hu' h') (range_γ W T π' c hx)

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨m, a, y, ⟨hy, heq⟩, -⟩`. Rewrite using `[SetLike.mem_coe, mem_LamLA, heq]`. Conclude with `rep_mem W T π' c _ (fun j => (a j).2) y hy`.
-/
theorem NL_le_LamLA (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) :
    NL W T Pt π' Eπ h' c ≤ LamLA W T π' Eπ h' c ⊤ := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨m, a, y, ⟨hy, heq⟩, -⟩
  rw [SetLike.mem_coe, mem_LamLA, heq]
  exact rep_mem W T π' c _ (fun j => (a j).2) y hy

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨x, hx, rfl⟩` from `hz`. Take `⟨x₀, hx₀, rfl⟩` from `Submodule.mem_map.1 hx`. Rewrite using `[← W.φγ_comm]`.

Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨W.γD T g (((letE (c - 1) : LetA O n) • LinearMap.id) x₀), ?_, rfl⟩` and prove the remaining obligations. Use `show W.γD T g ((letE (c - 1) : LetA O n) • x₀) ∈ W.Nl T (c - 1)`. Rewrite using `[γD_letE]`. Conclude with `⟨W.γD T g x₀, W.N_Γ T g x₀ hx₀, rfl⟩`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem φspan_γ (g : W.Gam) {z : W.DD T} (hz : z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))) :
    W.γD T g z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.1 hx
    rw [← W.φγ_comm]
    apply Submodule.subset_span
    refine ⟨W.γD T g (((letE (c - 1) : LetA O n) • LinearMap.id) x₀), ?_, rfl⟩
    show W.γD T g ((letE (c - 1) : LetA O n) • x₀) ∈ W.Nl T (c - 1)
    rw [γD_letE]
    exact ⟨W.γD T g x₀, W.N_Γ T g x₀ hx₀, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_DelS]`. Introduce `δ hδ`. Rewrite using `[← W.γD_mul, mul_comm, W.γD_mul, hx δ hδ]`.
-/
theorem DelS_γ (g : W.Gam) {x : W.DD T} (hx : x ∈ DelS W T) : W.γD T g x ∈ DelS W T := by
  rw [mem_DelS] at hx ⊢
  intro δ hδ
  rw [← W.γD_mul, mul_comm, W.γD_mul, hx δ hδ]

/- English proof (translation)
Rewrite `hy`, the goal using `[mem_LamPS]`. Take `⟨h1, h2, h3⟩` from `hy`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e : Eπ ^ h' = u' ^ h' * W.γA W.gamK (Eπ ^ h')`. Rewrite using `[map_pow, hγE, mul_pow, ← mul_assoc, ← mul_pow, huu, one_pow, one_mul]`.

Rewrite using `[e, mul_smul, ← Formalism.MainNotions.LiftingTheory.wmap_γD_smul]`. Conclude with `Submodule.smul_mem _ _ (φspan_γ W T c _ h1)`. Conclude with `(mem_DelS W T _).1 (DelS_γ W T _ ((mem_DelS W T y).2 h2))`. Rewrite using `[← γD_letE, h3]`.
-/
theorem LamPS_γ {u u' : LetA O n} (huu : u' * u = 1) (hγE : W.γA W.gamK Eπ = u * Eπ) {y : W.DD T}
    (hy : y ∈ LamPS W T Eπ h' c) : W.γD T W.gamK y ∈ LamPS W T Eπ h' c := by
  rw [mem_LamPS] at hy ⊢
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · have e : Eπ ^ h' = u' ^ h' * W.γA W.gamK (Eπ ^ h') := by
      rw [map_pow, hγE, mul_pow, ← mul_assoc, ← mul_pow, huu, one_pow, one_mul]
    rw [e, mul_smul, ← Formalism.MainNotions.LiftingTheory.wmap_γD_smul]
    exact Submodule.smul_mem _ _ (φspan_γ W T c _ h1)
  · exact (mem_DelS W T _).1 (DelS_γ W T _ ((mem_DelS W T y).2 h2))
  · rw [← γD_letE, h3]

/- English proof (translation)
Rewrite `hy`, the goal using `[mem_LamPS]`. Take `⟨h1, h2, h3⟩` from `hy`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm]`. Conclude with `Submodule.smul_mem _ _ h1`.

Introduce `δ hδ`. Rewrite using `[Formalism.MainNotions.LiftingTheory.wmap_γD_smul, ha δ hδ, h2 δ hδ]`. Rewrite using `[smul_comm, h3]`.
-/
theorem LamPS_smul {a : LetA O n} (ha : a ∈ W.AΔ) {y : W.DD T} (hy : y ∈ LamPS W T Eπ h' c) :
    a • y ∈ LamPS W T Eπ h' c := by
  rw [mem_LamPS] at hy ⊢
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · rw [smul_comm]
    exact Submodule.smul_mem _ _ h1
  · intro δ hδ
    rw [Formalism.MainNotions.LiftingTheory.wmap_γD_smul, ha δ hδ, h2 δ hδ]
  · rw [smul_comm, h3]

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨x, hx, rfl⟩` from `hz`. Establish `e : Eπ ^ h' = w' ^ h' * W.Q ^ h'`. Rewrite using `[hQ, mul_pow, ← mul_assoc, ← mul_pow, hww, one_pow, one_mul]`.

Rewrite using `[e, mul_smul]`. Conclude with `Submodule.smul_mem _ _ (h5 x hx)`. Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem Eπ_φspan {w : LetA O n} {w' : LetA O n} (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    (h5 : ∀ x ∈ W.Nl T (c - 1), W.Q ^ h' • W.φD T x ∈ W.N T) {z : W.DD T}
    (hz : z ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))) : Eπ ^ h' • z ∈ W.N T := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    have e : Eπ ^ h' = w' ^ h' * W.Q ^ h' := by
      rw [hQ, mul_pow, ← mul_assoc, ← mul_pow, hww, one_pow, one_mul]
    rw [e, mul_smul]
    exact Submodule.smul_mem _ _ (h5 x hx)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Take `⟨p, hp, rfl⟩` from `Submodule.mem_map.1 hy`. Establish `hpφ : p ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))` using `hp.1.1`. Use `⟨(π' ^ (M - j) * Eπ ^ (2 * h')) • (Eπ ^ h' • p), Submodule.smul_mem _ _ (Eπ_φspan W T Eπ h' c hww hQ h5 hpφ), ?_⟩` and prove the remaining obligations. Use `show (π' ^ M * Eπ ^ (3 * h')) • p = _`. Rewrite using `[smul_smul, smul_smul]`.

Use `congr 1`. Rewrite using `[show 3 * h' = 2 * h' + h' by ring, pow_add Eπ]`. Use `conv_lhs => rw [show M = j + (M - j) by omega, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem JP_mem {w w' : LetA O n} (hww : w' * w = 1) (hQ : W.Q = w * Eπ)
    (h5 : ∀ x ∈ W.Nl T (c - 1), W.Q ^ h' • W.φD T x ∈ W.N T) (M j : ℕ) (hj : j ≤ M) {y : W.DD T}
    (hy : y ∈ JP W T π' Eπ h' M c) : ∃ z ∈ W.N T, y = π' ^ j • z := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hy
  have hpφ : p ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1)) := hp.1.1
  refine ⟨(π' ^ (M - j) * Eπ ^ (2 * h')) • (Eπ ^ h' • p),
    Submodule.smul_mem _ _ (Eπ_φspan W T Eπ h' c hww hQ h5 hpφ), ?_⟩
  show (π' ^ M * Eπ ^ (3 * h')) • p = _
  rw [smul_smul, smul_smul]
  congr 1
  rw [show 3 * h' = 2 * h' + h' by ring, pow_add Eπ]
  conv_lhs => rw [show M = j + (M - j) by omega, pow_add]
  ring

/- English proof (translation)
Take `⟨u, hu⟩` from `ha`. Establish `h1 : (u : W.EE) • x = 0` using `by rw [hu, algebraMap_smul]; exact hx`. Establish `h2` using `congrArg (fun y => ((u⁻¹ : W.EEˣ) : W.EE) • y) h1`. Simplify `h2` using `[smul_smul]`.
-/
theorem tf_smul {a : LetA O n} (ha : IsUnit (algebraMap (LetA O n) W.EE a)) {x : W.DD T}
    (hx : a • x = 0) : x = 0 := by
  obtain ⟨u, hu⟩ := ha
  have h1 : (u : W.EE) • x = 0 := by rw [hu, algebraMap_smul]; exact hx
  have h2 := congrArg (fun y => ((u⁻¹ : W.EEˣ) : W.EE) • y) h1
  simpa [smul_smul] using h2

end Mod

end Formalism.MainNotions.N.Ln34.ModelFPf

end
