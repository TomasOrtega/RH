import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupForPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePairingSandwichStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInOfIntegers

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.PointGroup

/- English proof (translation)
Use `set S := LinearMap.range (HTLat.Tate.map p f)`. Establish `h1 : ∀ t, (p : ℤ_[p]) • t ∈ S → t ∈ S`. Introduce and unpack `t ⟨u, hu⟩`. Establish `h : ∀ n, f (u.lev (n + 1)) = t.lev n` using `fun n => by`. Rewrite using `[← HTLat.Tate.lev_map, hu, HTLat.Tate.lev_smul, PDiv.pow_digit_natCast (t.lev_pow _), t.lev_succ]`.

Conclude with `⟨HTLat.Tate.mk (fun n => u.lev (n + 1)) fun n => ⟨hf (by rw [map_pow, h, t.lev_pow, map_one]), u.lev_succ _⟩, HTLat.Tate.ext h⟩`. Establish `h2 : ∀ (n : ℕ) t, (p : ℤ_[p]) ^ n • t ∈ S → t ∈ S` using `fun n => by`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => exact fun t ht => h1 t (ih _ (by rwa [smul_smul, ← pow_succ]))`.

Use `haveI : Module.IsTorsionFree ℤ_[p] (HTLat.Tate p M' ⧸ S) := .of_smul_eq_zero fun a q h => by`. Distinguish the cases in `ha : a = 0`. Conclude with `.inl ha`. Take `⟨t, rfl⟩` from `S.mkQ_surjective q`. Rewrite `h` using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, PadicInt.unitCoeff_spec ha, mul_smul]`.

Conclude with `.inr ((Submodule.Quotient.mk_eq_zero _).2 (h2 _ t ((S.smul_mem_iff' (PadicInt.unitCoeff ha)).1 h)))`. Take `⟨σ, hσ⟩` from `Module.projective_lifting_property S.mkQ LinearMap.id S.mkQ_surjective`. Use `⟨(LinearMap.id - σ ∘ₗ S.mkQ).codRestrict S fun t => ?_, fun s => Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `s.1 - σ (S.mkQ s.1) = s.1`. Rewrite using `[Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 s.2, map_zero, sub_zero]`.

Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub]`. Conclude with `sub_eq_zero.2 (LinearMap.congr_fun hσ (S.mkQ t)).symm`.
-/
theorem exists_retraction {p : ℕ} [Fact p.Prime] {M M' : Type} [CommGroup M] [CommGroup M']
    (f : M →* M') (hf : Function.Injective f) [Module.Finite ℤ_[p] (HTLat.Tate p M')] :
    ∃ r : HTLat.Tate p M' →ₗ[ℤ_[p]] LinearMap.range (HTLat.Tate.map p f),
      ∀ s : LinearMap.range (HTLat.Tate.map p f), r s = s := by
  set S := LinearMap.range (HTLat.Tate.map p f)
  have h1 : ∀ t, (p : ℤ_[p]) • t ∈ S → t ∈ S := by
    rintro t ⟨u, hu⟩
    have h : ∀ n, f (u.lev (n + 1)) = t.lev n := fun n => by
      rw [← HTLat.Tate.lev_map, hu, HTLat.Tate.lev_smul, PDiv.pow_digit_natCast (t.lev_pow _),
        t.lev_succ]
    exact ⟨HTLat.Tate.mk (fun n => u.lev (n + 1)) fun n =>
      ⟨hf (by rw [map_pow, h, t.lev_pow, map_one]), u.lev_succ _⟩, HTLat.Tate.ext h⟩
  have h2 : ∀ (n : ℕ) t, (p : ℤ_[p]) ^ n • t ∈ S → t ∈ S := fun n => by
    induction n with
    | zero => simp
    | succ n ih => exact fun t ht => h1 t (ih _ (by rwa [smul_smul, ← pow_succ]))
  haveI : Module.IsTorsionFree ℤ_[p] (HTLat.Tate p M' ⧸ S) := .of_smul_eq_zero fun a q h => by
    by_cases ha : a = 0
    · exact .inl ha
    obtain ⟨t, rfl⟩ := S.mkQ_surjective q
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      PadicInt.unitCoeff_spec ha, mul_smul] at h
    exact .inr ((Submodule.Quotient.mk_eq_zero _).2 (h2 _ t ((S.smul_mem_iff' (PadicInt.unitCoeff ha)).1 h)))
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property S.mkQ LinearMap.id S.mkQ_surjective
  refine ⟨(LinearMap.id - σ ∘ₗ S.mkQ).codRestrict S fun t => ?_, fun s => Subtype.ext ?_⟩
  · change s.1 - σ (S.mkQ s.1) = s.1
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 s.2, map_zero, sub_zero]
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub]
    exact sub_eq_zero.2 (LinearMap.congr_fun hσ (S.mkQ t)).symm

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O]
  [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {Λ : Type} [CommRing Λ] [StarRing Λ]
  (P : Point p v O Λ)

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]`. Consider the case `tmul c s`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul d t`. Rewrite using `[P.inclT_tmul, P.inclT_tmul, P.pairV_tmul, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, ← IsScalarTower.algebraMap_apply]`.
-/
theorem pairV_inclT (x z : O ⊗[ℤ_[p]] P.T) : P.pairV (P.inclT x) (P.inclT z) =
    algebraMap O C (LinearMap.BilinForm.baseChange O (pairT P.A P.eps) x z) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul c s =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul d t =>
      rw [P.inclT_tmul, P.inclT_tmul, P.pairV_tmul, LinearMap.BilinForm.baseChange_tmul,
        Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Establish `h : ∀ x, P.inclT x = ((Algebra.linearMap O C).restrictScalars ℤ_[p]).rTensor P.T x` using `fun x => by`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul c s => rw [P.inclT_tmul]`.

Both sides reduce to the same expression. Introduce `x y hxy`. Rewrite `hxy` using `[h, h]`. Conclude with `Module.Flat.rTensor_preserves_injective_linearMap _ P.integers.hom_inj hxy`.
-/
theorem inclT_injective : Function.Injective P.inclT := by
  have h : ∀ x, P.inclT x = ((Algebra.linearMap O C).restrictScalars ℤ_[p]).rTensor P.T x :=
    fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul c s => rw [P.inclT_tmul]; rfl
  intro x y hxy
  rw [h, h] at hxy
  exact Module.Flat.rTensor_preserves_injective_linearMap _ P.integers.hom_inj hxy

omit [IsAlgClosed C] [CharZero C] in
/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul c s => rw [LinearMap.baseChange_tmul, P.inclT_tmul, P.inclT_tmul, LinearMap.baseChange_tmul]`.
-/
theorem inclT_baseChange (g : P.T →ₗ[ℤ_[p]] P.T) (x : O ⊗[ℤ_[p]] P.T) :
    P.inclT (g.baseChange O x) = g.baseChange C (P.inclT x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c s => rw [LinearMap.baseChange_tmul, P.inclT_tmul, P.inclT_tmul, LinearMap.baseChange_tmul]

/- English proof (translation)
Establish `h : (pairT P.A P.eps).flip = -pairT P.A P.eps` using `LinearMap.ext₂ fun s t => ((isAlt_pairT P.A P.eps).neg_eq s t).symm`. Rewrite using `[h]`. Conclude with `neg_bijective.comp P.pairT_bijective`.
-/
theorem pairT_flip_bijective : Function.Bijective (pairT P.A P.eps).flip := by
  have h : (pairT P.A P.eps).flip = -pairT P.A P.eps :=
    LinearMap.ext₂ fun s t => ((isAlt_pairT P.A P.eps).neg_eq s t).symm
  rw [h]
  exact neg_bijective.comp P.pairT_bijective

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

/- English proof (translation)
Rewrite `h` using `[← algebraMap_smul C c]`. Conclude with `(P.W.smul_mem_iff ((map_ne_zero_iff _ P.integers.hom_inj).2 hc)).1 h`.
-/
theorem mem_W_of_smul {c : O} (hc : c ≠ 0) {w : P.V} (h : c • w ∈ P.W) : w ∈ P.W := by
  rw [← algebraMap_smul C c] at h
  exact (P.W.smul_mem_iff ((map_ne_zero_iff _ P.integers.hom_inj).2 hc)).1 h

/- English proof (translation)
Establish `h5` using `K.2.2.2.2.1`. Use `⟨fun hz x hx => P.integers.hom_inj ?_, fun h => (h5 _).2 fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[← pairV_inclT, map_zero]`. Conclude with `(h5 _).1 hx _ hz`. Take `⟨a, ha, x, hx⟩` from `P.exists_smul_mem_latT y`.

Establish `h1` using `pairV_inclT P x z`. Rewrite `h1` using `[h x (by rw [hx, ← algebraMap_smul C a]; exact P.W.smul_mem _ hy), map_zero, hx, ← algebraMap_smul C a, map_smul, LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[P.pairV_swap, (mul_eq_zero.1 h1).resolve_left ((map_ne_zero_iff _ P.integers.hom_inj).2 ha), neg_zero]`.
-/
theorem inclT_mem_W_iff (K : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.KernelShape P) (z : O ⊗[ℤ_[p]] P.T) :
    P.inclT z ∈ P.W ↔ ∀ x, P.inclT x ∈ P.W →
      LinearMap.BilinForm.baseChange O (pairT P.A P.eps) x z = 0 := by
  have h5 := K.2.2.2.2.1
  refine ⟨fun hz x hx => P.integers.hom_inj ?_, fun h => (h5 _).2 fun y hy => ?_⟩
  · rw [← pairV_inclT, map_zero]
    exact (h5 _).1 hx _ hz
  · obtain ⟨a, ha, x, hx⟩ := P.exists_smul_mem_latT y
    have h1 := pairV_inclT P x z
    rw [h x (by rw [hx, ← algebraMap_smul C a]; exact P.W.smul_mem _ hy), map_zero, hx,
      ← algebraMap_smul C a, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [P.pairV_swap, (mul_eq_zero.1 h1).resolve_left ((map_ne_zero_iff _ P.integers.hom_inj).2 ha),
      neg_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[K.2.2.2.2.2.2]`. Introduce `hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩`.

Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hx⟩` from `hx`. Take `⟨b, hb, hy⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Rewrite using `[mul_smul]`.

Conclude with `Submodule.smul_mem _ _ hy`. Consider the case `smul d x _ hx`. Take `⟨a, ha, hx⟩` from `hx`. Use `haveI := P.integers.isFractionRing`. Take `⟨⟨n, b⟩, hb⟩` from `IsLocalization.surj (nonZeroDivisors O) d`.

Use `⟨a * b, mul_ne_zero ha (nonZeroDivisors.ne_zero b.2), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, ← algebraMap_smul C (b : O), smul_smul _ d, mul_comm _ d, hb, algebraMap_smul, smul_comm]`. Conclude with `Submodule.smul_mem _ _ hx`. Introduce and unpack `⟨c, hc, z, hz⟩`. Use `mem_W_of_smul P hc ?_` and prove the remaining obligations.

Rewrite using `[← hz, K.2.2.2.2.2.2]`. Conclude with `Submodule.subset_span ⟨z, rfl⟩`.
-/
theorem mem_W_iff [IsDomain O] (K : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.KernelShape P) (w : P.V) :
    w ∈ P.W ↔ ∃ c : O, c ≠ 0 ∧ c • w ∈ P.latLie := by
  constructor
  · rw [K.2.2.2.2.2.2]
    intro hw
    induction hw using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨b, hb, hy⟩ := hy
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      rw [smul_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul d x _ hx =>
      obtain ⟨a, ha, hx⟩ := hx
      haveI := P.integers.isFractionRing
      obtain ⟨⟨n, b⟩, hb⟩ := IsLocalization.surj (nonZeroDivisors O) d
      refine ⟨a * b, mul_ne_zero ha (nonZeroDivisors.ne_zero b.2), ?_⟩
      rw [mul_smul, ← algebraMap_smul C (b : O), smul_smul _ d, mul_comm _ d, hb, algebraMap_smul,
        smul_comm]
      exact Submodule.smul_mem _ _ hx
  · rintro ⟨c, hc, z, hz⟩
    refine mem_W_of_smul P hc ?_
    rw [← hz, K.2.2.2.2.2.2]
    exact Submodule.subset_span ⟨z, rfl⟩

/- English proof (translation)
Establish `h1 : Function.Surjective c` using `fun χ => by`. Take `⟨t, ht⟩` from `(pairT_flip_bijective P).2 (B.flip χ ∘ₗ r)`. Use `⟨t, hB (LinearMap.ext fun s => (hc s t).trans ?_)⟩` and prove the remaining obligations. Conclude with `(LinearMap.congr_fun ht (j s)).trans (by rw [LinearMap.comp_apply, hr])`. Establish `h2 : ∀ t, P.pairV (P.inclT (j.baseChange O x)) (1 ⊗ₜ t) = algebraMap O C (TensorProduct.rid ℤ_[p] O ((B.flip (c t)).baseChange O x))` using `fun t => by`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]`. Consider the case `tmul a s`. Rewrite using `[LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, P.inclT_tmul, P.pairV_tmul, LinearMap.flip_apply, hc, TensorProduct.rid_tmul, mul_one, Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]`.

Establish `h3 : ∀ (a : O) t, P.pairV (a • P.inclT (j.baseChange O x)) (1 ⊗ₜ t) = algebraMap O C (a * TensorProduct.rid ℤ_[p] O ((B.flip (c t)).baseChange O x))` using `fun a t => by`. Rewrite using `[← algebraMap_smul C a, map_smul, LinearMap.smul_apply, h2, smul_eq_mul, map_mul]`. Rewrite using `[hk x, mem_W_iff P K]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, y, ha, h⟩`.

Take `⟨z, rfl⟩` from `l.surjective y`. Conclude with `⟨a, ha, z, P.eq_of_pairV fun t => by rw [h3, h, hl, P.pairV_bLie]⟩`. Introduce and unpack `⟨a, ha, z, hz⟩`. Use `⟨a, l z, ha, fun χ => ?_⟩` and prove the remaining obligations. Take `⟨t, rfl⟩` from `h1 χ`.

Conclude with `P.integers.hom_inj (by rw [← h3, ← hz, hl, P.pairV_bLie])`.
-/
theorem ker_iff_of_weil [IsDomain O] (K : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.KernelShape P) {G : PDivGroup p O}
    (j : G.Tate →ₗ[ℤ_[p]] P.T) (r : P.T →ₗ[ℤ_[p]] G.Tate) (hr : ∀ s, r (j s) = s)
    (l : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt ≃ G.Lie) (c : P.T →ₗ[ℤ_[p]] G.dual.Tate)
    (B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p]) (hB : Function.Injective B.flip)
    (hk : KerIsLie G B) (hc : ∀ s t, B s (c t) = pairT P.A P.eps (j s) t)
    (hl : ∀ x t, l x (dlog G (c t)) = (P.al₀ t).1 x) (x : O ⊗[ℤ_[p]] G.Tate) :
    G.hodgeTateLinear x = 0 ↔ P.inclT (j.baseChange O x) ∈ P.W := by
  have h1 : Function.Surjective c := fun χ => by
    obtain ⟨t, ht⟩ := (pairT_flip_bijective P).2 (B.flip χ ∘ₗ r)
    refine ⟨t, hB (LinearMap.ext fun s => (hc s t).trans ?_)⟩
    exact (LinearMap.congr_fun ht (j s)).trans (by rw [LinearMap.comp_apply, hr])
  have h2 : ∀ t, P.pairV (P.inclT (j.baseChange O x)) (1 ⊗ₜ t) =
      algebraMap O C (TensorProduct.rid ℤ_[p] O ((B.flip (c t)).baseChange O x)) := fun t => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul a s =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, P.inclT_tmul, P.pairV_tmul,
        LinearMap.flip_apply, hc, TensorProduct.rid_tmul, mul_one, Algebra.smul_def,
        Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  have h3 : ∀ (a : O) t, P.pairV (a • P.inclT (j.baseChange O x)) (1 ⊗ₜ t) =
      algebraMap O C (a * TensorProduct.rid ℤ_[p] O ((B.flip (c t)).baseChange O x)) := fun a t => by
    rw [← algebraMap_smul C a, map_smul, LinearMap.smul_apply, h2, smul_eq_mul, map_mul]
  rw [hk x, mem_W_iff P K]
  constructor
  · rintro ⟨a, y, ha, h⟩
    obtain ⟨z, rfl⟩ := l.surjective y
    exact ⟨a, ha, z, P.eq_of_pairV fun t => by rw [h3, h, hl, P.pairV_bLie]⟩
  · rintro ⟨a, ha, z, hz⟩
    refine ⟨a, l z, ha, fun χ => ?_⟩
    obtain ⟨t, rfl⟩ := h1 χ
    exact P.integers.hom_inj (by rw [← h3, ← hz, hl, P.pairV_bLie])

/- English proof (translation)
Take `⟨b⟩` from `P.nonempty_T_equiv`. Take `⟨G, e, h⟩` from `(SW p C v O P.integers).2 _ ((P.W.restrictScalars O).comap (P.inclT ∘ₗ b.symm.toLinearMap.baseChange O)) fun c x hc hx => mem_W_of_smul P hc (by rw [← map_smul]; exact hx)`. Use `⟨G, e.trans b.symm, fun x => (h x).trans ?_⟩` and prove the remaining obligations. Rewrite using `[LinearEquiv.coe_trans, LinearMap.baseChange_comp]`. Both sides reduce to the same expression.
-/
theorem exists_group (SW : GlobalTheory.Published.ScholzeWeinsteinB) :
    ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.T), ∀ x, G.hodgeTateLinear x = 0 ↔
      P.inclT (e.toLinearMap.baseChange O x) ∈ P.W := by
  obtain ⟨b⟩ := P.nonempty_T_equiv
  obtain ⟨G, e, h⟩ := (SW p C v O P.integers).2 _
    ((P.W.restrictScalars O).comap (P.inclT ∘ₗ b.symm.toLinearMap.baseChange O))
    fun c x hc hx => mem_W_of_smul P hc (by rw [← map_smul]; exact hx)
  refine ⟨G, e.trans b.symm, fun x => (h x).trans ?_⟩
  rw [LinearEquiv.coe_trans, LinearMap.baseChange_comp]
  rfl

/- English proof (translation)
Establish `h : Module.Finite ℤ_[p] P.T` using `inferInstance`. Unfold `Point.tateGt`. Conclude with `@exists_retraction p _ _ _ (_) (_) _ P.toA_injective h`.
-/
theorem exists_retraction_tateGt :
    ∃ r : P.T →ₗ[ℤ_[p]] P.tateGt, ∀ s : P.tateGt, r s = s := by
  have h : Module.Finite ℤ_[p] P.T := inferInstance
  unfold Point.tateGt
  exact @exists_retraction p _ _ _ (_) (_) _ P.toA_injective h

omit [IsAlgClosed C] [CharZero C] in
/- English proof (translation)
Take `⟨w, rfl⟩` from `hw`. Establish `h : g ∘ₗ S.subtype = S.subtype` using `LinearMap.ext hg`. Rewrite using `[← LinearMap.comp_apply, ← LinearMap.baseChange_comp, h]`.
-/
theorem baseChange_eq_self {T : Type} [AddCommGroup T] [Module ℤ_[p] T] (S : Submodule ℤ_[p] T)
    (g : T →ₗ[ℤ_[p]] T) (hg : ∀ s : S, g s = s) (w : C ⊗[ℤ_[p]] T) (hw : w ∈ S.baseChange C) :
    g.baseChange C w = w := by
  obtain ⟨w, rfl⟩ := hw
  have h : g ∘ₗ S.subtype = S.subtype := LinearMap.ext hg
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, h]

section Group

variable {G : PDivGroup p O} (e : G.Tate ≃ₗ[ℤ_[p]] P.T)

omit [IsAlgClosed C] [CharZero C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] in
/- English proof (translation)
Rewrite using `[← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.id_comp]`.
-/
theorem baseChange_symm_comp {N : Type} [AddCommGroup N] [Module ℤ_[p] N] (g : N →ₗ[ℤ_[p]] P.T)
    (x : O ⊗[ℤ_[p]] N) :
    e.toLinearMap.baseChange O ((e.symm.toLinearMap ∘ₗ g).baseChange O x) = g.baseChange O x := by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.comp_assoc,
    LinearEquiv.comp_symm, LinearMap.id_comp]

variable (SW : GlobalTheory.Published.ScholzeWeinsteinB) (K : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.KernelShape P)
  (hG : ∀ x, G.hodgeTateLinear x = 0 ↔ P.inclT (e.toLinearMap.baseChange O x) ∈ P.W)

include SW K hG

/- English proof (translation)
Take `⟨ρ, hρ⟩` from `exists_action SW P.integers G (e.symm.conjRingEquiv.toRingHom.comp P.actT) fun a x hx => (hG _).2 (by`. Establish `h : (e.symm.conjRingEquiv.toRingHom.comp P.actT) a = e.symm.toLinearMap ∘ₗ (P.actT a ∘ₗ e.toLinearMap)` using `rfl`. Rewrite using `[h, baseChange_symm_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, inclT_baseChange]`. Conclude with `K.2.1 a _ ((hG x).1 hx))`. Conclude with `⟨ρ, fun a t => by rw [hρ]; exact e.apply_symm_apply _⟩`.
-/
theorem exists_action_point : ∃ ρ : Action (ℤ_[p] ⊗[ℤ] Λ) G,
    ∀ (a : Λ) t, e (ρ.onTate O (1 ⊗ₜ a) t) = P.actT a (e t) := by
  obtain ⟨ρ, hρ⟩ := exists_action SW P.integers G (e.symm.conjRingEquiv.toRingHom.comp P.actT)
    fun a x hx => (hG _).2 (by
      have h : (e.symm.conjRingEquiv.toRingHom.comp P.actT) a =
        e.symm.toLinearMap ∘ₗ (P.actT a ∘ₗ e.toLinearMap) := rfl
      rw [h, baseChange_symm_comp, LinearMap.baseChange_comp, LinearMap.comp_apply,
        inclT_baseChange]
      exact K.2.1 a _ ((hG x).1 hx))
  exact ⟨ρ, fun a t => by rw [hρ]; exact e.apply_symm_apply _⟩

variable [IsDomain O] {ε : PreTilt O p} {hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε}
  (H : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε) {ζ : (PDivGroup.mu p O).Tate}
  (hζ : Function.Bijective fun a : ℤ_[p] => a • ζ)

include H hζ

/- English proof (translation)
Establish `hv` using `P.integers`. Take `⟨B, hB, hB1, hB2⟩` from `exists_form hv G ζ hζ`. Establish `hk : KerIsLie G B` using `(GlobalTheory.T.hodge_tate_pairing_sandwich p C v O ε hε H G ζ B hv hζ hB).1`. Establish `hβ : ∀ x z, LinearMap.BilinForm.baseChange O ((pairT P.A P.eps).compl₁₂ e.toLinearMap e.toLinearMap) x z = LinearMap.BilinForm.baseChange O (pairT P.A P.eps) (e.toLinearMap.baseChange O x) (e.toLinearMap.baseChange O z)` using `fun x z => by`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]`. Consider the case `tmul c s`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul d t => simp`. Establish `hb : Function.Bijective ((pairT P.A P.eps).compl₁₂ e.toLinearMap e.toLinearMap).flip`. Establish `h : ((pairT P.A P.eps).compl₁₂ e.toLinearMap e.toLinearMap).flip = e.dualMap.toLinearMap ∘ₗ (pairT P.A P.eps).flip ∘ₗ e.toLinearMap`. Use extensionality with `s t`.

Simplify using the standard rewrite rules. Rewrite using `[h, LinearMap.coe_comp, LinearMap.coe_comp]`. Conclude with `e.dualMap.bijective.comp ((pairT_flip_bijective P).comp e.bijective)`. Use `exists_pol SW hv H G ζ B hB hB1.2 hB2 hk ((pairT P.A P.eps).compl₁₂ e.toLinearMap e.toLinearMap) hb fun z => ?_` and prove the remaining obligations. Rewrite using `[hG, inclT_mem_W_iff P K]`.

Use `⟨fun h x hx => by rw [hβ, h _ ((hG x).1 hx)], fun h x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `baseChange_symm_comp P e LinearMap.id x`. Rewrite `h1` using `[LinearMap.baseChange_id, LinearMap.id_apply]`. Rewrite using `[← h1, ← hβ]`. Conclude with `h _ ((hG _).2 (by rwa [h1]))`.
-/
theorem exists_pol_point : ∃ pol : G ≅ G.dual, ∀ s t,
    pairing G O s (tateMap G G.dual O pol.hom t) = pairT P.A P.eps (e s) (e t) • ζ := by
  have hv := P.integers
  obtain ⟨B, hB, hB1, hB2⟩ := exists_form hv G ζ hζ
  have hk : KerIsLie G B := (GlobalTheory.T.hodge_tate_pairing_sandwich p C v O ε hε H G ζ B hv hζ hB).1
  have hβ : ∀ x z, LinearMap.BilinForm.baseChange O
      ((pairT P.A P.eps).compl₁₂ e.toLinearMap e.toLinearMap) x z =
      LinearMap.BilinForm.baseChange O (pairT P.A P.eps) (e.toLinearMap.baseChange O x)
        (e.toLinearMap.baseChange O z) := fun x z => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul c s =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul d t => simp
  have hb : Function.Bijective ((pairT P.A P.eps).compl₁₂ e.toLinearMap e.toLinearMap).flip := by
    have h : ((pairT P.A P.eps).compl₁₂ e.toLinearMap e.toLinearMap).flip =
      e.dualMap.toLinearMap ∘ₗ (pairT P.A P.eps).flip ∘ₗ e.toLinearMap := by
      ext s t; simp
    rw [h, LinearMap.coe_comp, LinearMap.coe_comp]
    exact e.dualMap.bijective.comp ((pairT_flip_bijective P).comp e.bijective)
  refine exists_pol SW hv H G ζ B hB hB1.2 hB2 hk
    ((pairT P.A P.eps).compl₁₂ e.toLinearMap e.toLinearMap) hb fun z => ?_
  rw [hG, inclT_mem_W_iff P K]
  refine ⟨fun h x hx => by rw [hβ, h _ ((hG x).1 hx)], fun h x hx => ?_⟩
  have h1 := baseChange_symm_comp P e LinearMap.id x
  rw [LinearMap.baseChange_id, LinearMap.id_apply] at h1
  rw [← h1, ← hβ]
  exact h _ ((hG _).2 (by rwa [h1]))

/- English proof (translation)
Establish `hv` using `P.integers`. Take `⟨B, hB, hB1, -⟩` from `exists_form hv G ζ hζ`. Take `⟨B₁, hB₁, -, hB₁2⟩` from `exists_form hv G₁ ζ hζ`. Establish `hk : KerIsLie G B` using `(GlobalTheory.T.hodge_tate_pairing_sandwich p C v O ε hε H G ζ B hv hζ hB).1`. Establish `hk₁ : KerIsLie G₁ B₁` using `(GlobalTheory.T.hodge_tate_pairing_sandwich p C v O ε hε H G₁ ζ B₁ hv hζ hB₁).1`.

Take `⟨r, hr⟩` from `exists_retraction_tateGt P`. Take `⟨j, hj⟩ : ∃ j : G₁.Tate →ₗ[ℤ_[p]] P.T, ∀ s, j s = e₁ s` from `⟨P.tateGt.subtype ∘ₗ e₁.toLinearMap, fun _ => rfl⟩`. Take `⟨r₁, hr'⟩ : ∃ r₁ : P.T →ₗ[ℤ_[p]] G₁.Tate, ∀ t, r₁ t = e₁.symm (r t)` from `⟨e₁.symm.toLinearMap ∘ₗ r, fun _ => rfl⟩`. Establish `hr₁ : ∀ s, r₁ (j s) = s` using `fun s => by rw [hj, hr', hr, e₁.symm_apply_apply]`. Establish `hc₁ : ∀ s t, B₁ s (c t) = pairT P.A P.eps (j s) t` using `fun s t => by`.

Rewrite using `[hj]`. Conclude with `hζ.1 ((hB₁ s _).symm.trans (hc s t))`. Establish `hfix` using `baseChange_eq_self (C := C) P.tateGt (j ∘ₗ r₁) fun s => by`. Rewrite using `[LinearMap.comp_apply, hj, hr', e₁.apply_symm_apply, hr]`. Establish `he : Function.Injective (e.toLinearMap.baseChange O)` using `(e.baseChange ℤ_[p] O _ _).injective`.

Establish `h1 : ∀ s, (r₁ ∘ₗ e.toLinearMap) ((e.symm.toLinearMap ∘ₗ j) s) = s` using `fun s => by`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hr₁]`. Establish `h2 : ∀ x, G₁.hodgeTateLinear x = 0 ↔ G.hodgeTateLinear ((e.symm.toLinearMap ∘ₗ j).baseChange O x) = 0` using `fun x => by`. Rewrite using `[hG, baseChange_symm_comp]`. Conclude with `ker_iff_of_weil P K j r₁ hr₁ l₁ c B₁ hB₁2.1 hk₁ hc₁ hl x`.

Establish `h3 : ∀ x, G.hodgeTateLinear x = 0 → (e.symm.toLinearMap ∘ₗ j).baseChange O ((r₁ ∘ₗ e.toLinearMap).baseChange O x) = x` using `fun x hx => by`. Use `he (inclT_injective P ?_)` and prove the remaining obligations. Rewrite using `[baseChange_symm_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, ← LinearMap.comp_apply (j.baseChange O), ← LinearMap.baseChange_comp, inclT_baseChange]`. Conclude with `hfix _ (K.2.2.2.1 ((hG x).1 hx))`. Take `⟨i, hi, hi'⟩` from `exists_lie_bijective SW hv H G G₁ ζ hζ.1 B hB hB1.2 hk _ _ h1 h2 h3`.

Conclude with `⟨i, fun s => by rw [hi, ← hj]; exact e.apply_symm_apply _, hi'⟩`.
-/
theorem exists_lie_point {G₁ : PDivGroup p O} (e₁ : G₁.Tate ≃ₗ[ℤ_[p]] P.tateGt)
    (l₁ : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt ≃ G₁.Lie) (c : P.T →ₗ[ℤ_[p]] G₁.dual.Tate)
    (hc : ∀ s t, pairing G₁ O s (c t) = pairT P.A P.eps (e₁ s : P.T) t • ζ)
    (hl : ∀ x t, l₁ x (dlog G₁ (c t)) = (P.al₀ t).1 x) :
    ∃ i : G₁ ⟶ G, (∀ s, e (tateMap G₁ G O i s) = e₁ s) ∧ Function.Bijective (lieMap G₁ G i) := by
  have hv := P.integers
  obtain ⟨B, hB, hB1, -⟩ := exists_form hv G ζ hζ
  obtain ⟨B₁, hB₁, -, hB₁2⟩ := exists_form hv G₁ ζ hζ
  have hk : KerIsLie G B := (GlobalTheory.T.hodge_tate_pairing_sandwich p C v O ε hε H G ζ B hv hζ hB).1
  have hk₁ : KerIsLie G₁ B₁ := (GlobalTheory.T.hodge_tate_pairing_sandwich p C v O ε hε H G₁ ζ B₁ hv hζ hB₁).1
  obtain ⟨r, hr⟩ := exists_retraction_tateGt P
  obtain ⟨j, hj⟩ : ∃ j : G₁.Tate →ₗ[ℤ_[p]] P.T, ∀ s, j s = e₁ s :=
    ⟨P.tateGt.subtype ∘ₗ e₁.toLinearMap, fun _ => rfl⟩
  obtain ⟨r₁, hr'⟩ : ∃ r₁ : P.T →ₗ[ℤ_[p]] G₁.Tate, ∀ t, r₁ t = e₁.symm (r t) :=
    ⟨e₁.symm.toLinearMap ∘ₗ r, fun _ => rfl⟩
  have hr₁ : ∀ s, r₁ (j s) = s := fun s => by rw [hj, hr', hr, e₁.symm_apply_apply]
  have hc₁ : ∀ s t, B₁ s (c t) = pairT P.A P.eps (j s) t := fun s t => by
    rw [hj]
    exact hζ.1 ((hB₁ s _).symm.trans (hc s t))
  have hfix := baseChange_eq_self (C := C) P.tateGt (j ∘ₗ r₁) fun s => by
    rw [LinearMap.comp_apply, hj, hr', e₁.apply_symm_apply, hr]
  have he : Function.Injective (e.toLinearMap.baseChange O) := (e.baseChange ℤ_[p] O _ _).injective
  have h1 : ∀ s, (r₁ ∘ₗ e.toLinearMap) ((e.symm.toLinearMap ∘ₗ j) s) = s := fun s => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hr₁]
  have h2 : ∀ x, G₁.hodgeTateLinear x = 0 ↔
      G.hodgeTateLinear ((e.symm.toLinearMap ∘ₗ j).baseChange O x) = 0 := fun x => by
    rw [hG, baseChange_symm_comp]
    exact ker_iff_of_weil P K j r₁ hr₁ l₁ c B₁ hB₁2.1 hk₁ hc₁ hl x
  have h3 : ∀ x, G.hodgeTateLinear x = 0 → (e.symm.toLinearMap ∘ₗ j).baseChange O
      ((r₁ ∘ₗ e.toLinearMap).baseChange O x) = x := fun x hx => by
    refine he (inclT_injective P ?_)
    rw [baseChange_symm_comp, LinearMap.baseChange_comp, LinearMap.comp_apply,
      ← LinearMap.comp_apply (j.baseChange O), ← LinearMap.baseChange_comp, inclT_baseChange]
    exact hfix _ (K.2.2.2.1 ((hG x).1 hx))
  obtain ⟨i, hi, hi'⟩ := exists_lie_bijective SW hv H G G₁ ζ hζ.1 B hB hB1.2 hk _ _ h1 h2 h3
  exact ⟨i, fun s => by rw [hi, ← hj]; exact e.apply_symm_apply _, hi'⟩

end Group

/- English proof (translation)
Introduce `SW p _ C _ _ _ v O _ _ _ _ _ _ _ _ ε hε H Λ _ _ P K`. Take `⟨G₁, e₁, l₁, c, ζ, hζ, hc, hl⟩` from `GlobalTheory.T.exists_pdiv_group_for_point p C v O Λ P`. Take `⟨G, e, hG⟩` from `exists_group P SW`. Take `⟨ρ, hρ⟩` from `exists_action_point P e SW K hG`. Take `⟨pol, hpol⟩` from `exists_pol_point P e SW K hG H hζ`.

Take `⟨i, hi, hi'⟩` from `exists_lie_point P e SW K hG H hζ e₁ l₁ c hc hl`. Use `⟨G, e, ρ, pol, l₁.trans (Equiv.ofBijective _ hi'), ζ, hζ, hpol, fun x t => ?_, hρ⟩` and prove the remaining obligations. Use `isIntegrallyClosedIn_of_integers P.integers` as an intermediate fact. Establish `h1 : tateMap _ _ O (dualHom G₁ G i) (tateMap G G.dual O pol.hom t) = c (e t)` using `(G₁.pairing_flip_bijective C).1 (LinearMap.ext fun s => by`. Rewrite using `[LinearMap.flip_apply, LinearMap.flip_apply, ← pairing_tateMap, hpol, hi, hc])`.

Rewrite using `[Equiv.trans_apply, Equiv.ofBijective_apply, lieMap_apply, ← dlog_tateMap, h1, hl]`.
-/
theorem exists_selfDual_group : GlobalTheory.Published.ScholzeWeinsteinB → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.KernelShape P → ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.T) (ρ : Action (ℤ_[p] ⊗[ℤ] Λ) G) (pol : G ≅ G.dual) (l : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt ≃ G.Lie) (ζ : (PDivGroup.mu p O).Tate), Function.Bijective (fun a : ℤ_[p] => a • ζ) ∧ (∀ s t, pairing G O s (tateMap G G.dual O pol.hom t) = pairT P.A P.eps (e s) (e t) • ζ) ∧ (∀ x t, l x (dlog (G := G) (tateMap G G.dual O pol.hom t)) = (P.al₀ (e t)).1 x) ∧ ∀ (a : Λ) t, e (ρ.onTate O (1 ⊗ₜ a) t) = P.actT a (e t) := by
  intro SW p _ C _ _ _ v O _ _ _ _ _ _ _ _ ε hε H Λ _ _ P K
  obtain ⟨G₁, e₁, l₁, c, ζ, hζ, hc, hl⟩ := GlobalTheory.T.exists_pdiv_group_for_point p C v O Λ P
  obtain ⟨G, e, hG⟩ := exists_group P SW
  obtain ⟨ρ, hρ⟩ := exists_action_point P e SW K hG
  obtain ⟨pol, hpol⟩ := exists_pol_point P e SW K hG H hζ
  obtain ⟨i, hi, hi'⟩ := exists_lie_point P e SW K hG H hζ e₁ l₁ c hc hl
  refine ⟨G, e, ρ, pol, l₁.trans (Equiv.ofBijective _ hi'), ζ, hζ, hpol, fun x t => ?_, hρ⟩
  have := isIntegrallyClosedIn_of_integers P.integers
  have h1 : tateMap _ _ O (dualHom G₁ G i) (tateMap G G.dual O pol.hom t) = c (e t) :=
    (G₁.pairing_flip_bijective C).1 (LinearMap.ext fun s => by
      rw [LinearMap.flip_apply, LinearMap.flip_apply, ← pairing_tateMap, hpol, hi, hc])
  rw [Equiv.trans_apply, Equiv.ofBijective_apply, lieMap_apply, ← dlog_tateMap, h1, hl]

end GlobalTheory.PointGroup
