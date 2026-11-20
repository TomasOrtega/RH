import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UniformizerMemDeltaInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkDcrisLSumZero

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD
  Formalism.MainNotions.RamifiedCoefficientChains.S9.DCount

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

def DRFree : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      Module.Free O (RR W T₂ i (b i + S)) ∧ Module.Finite O (RR W T₂ i (b i + S))

def DRQEta : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d, ∀ x ∈ NDl W T₂ i,
      Formalism.MainNotions.LiftingTheory.qp W ^ η • x ∈ PhiPullΔ W T₂ i

def DRLat (hπ : W.π₀ ∈ W.AΔ) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∃ (m' : ℕ) (_ : m' ≤ m) (g : Fin m' → ↥(NDl W T₂ i)) (k : Fin m' → ℕ),
        (∃ e : ↥(RRp W T₂ hπ i (b i + S) g) ≃ₗ[O] ((j : Fin m') → Aq O (k j)),
          ∀ (x : ↥(RRp W T₂ hπ i (b i + S) g)) (j : Fin m'),
            e ⟨qR W T₂ hπ i (b i + S) x, RRp_stable W T₂ hπ i (b i + S) g x x.2⟩ j =
              Ideal.Quotient.mk _ PowerSeries.X * e x j) ∧
        (∀ (z : RR W T₂ i (b i + S)) (t : ℕ), ((PD.p : ℕ) : O) ^ t • z ∈ RRp W T₂ hπ i (b i + S) g →
          ((PD.p : ℕ) : O) ^ (2 * ⌊cD PD.p (hpar n b S + η)⌋₊) • z ∈ RRp W T₂ hπ i (b i + S) g) ∧
        finrank O (RR W T₂ i (b i + S) ⧸ satL ((PD.p : ℕ) : O) (RRp W T₂ hπ i (b i + S) g)) ≤
          finrank LL T₂.V * S

/- English proof (translation)
Establish `hq1 : ∀ y : ↥(NDl W T i), ((qN W T hπ i y : ↥(NDl W T i)) : W.DD T) = Formalism.MainNotions.LiftingTheory.qp W • (y : W.DD T)` using `fun y => rfl`. Establish `hpow : ∀ (k : ℕ) (y : ↥(NDl W T i)), (((qN W T hπ i ^ k) y : ↥(NDl W T i)) : W.DD T) = Formalism.MainNotions.LiftingTheory.qp W ^ k • (y : W.DD T)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro y`.

Simplify using the standard rewrite rules. Consider the case `succ k ih => intro y`. Rewrite using `[pow_succ', Module.End.mul_apply, hq1, ih, pow_succ', mul_smul]`. Use `⟨h + η, ?_⟩` and prove the remaining obligations. Unfold `qR`.

Rewrite using `[← Submodule.mapQ_pow]`. Use extensionality with `x`. Simplify using `only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.zero_comp, LinearMap.zero_apply]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Use `show (((qN W T hπ i ^ (h + η)) x : ↥(NDl W T i)) : W.DD T) ∈ QhP W T i h`.

Rewrite using `[hpow, pow_add, mul_smul]`. Unfold `QhP`. Conclude with `Submodule.mem_map.2 ⟨_, hq x x.2, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩`.
-/
theorem qR_nil_of (hπ : W.π₀ ∈ W.AΔ) (T : LocLat G Qp LL O) (i : ZMod n) (h η : ℕ)
    (hq : ∀ x ∈ NDl W T i, Formalism.MainNotions.LiftingTheory.qp W ^ η • x ∈ PhiPullΔ W T i) :
    IsNilpotent (qR W T hπ i h) := by
  have hq1 : ∀ y : ↥(NDl W T i),
      ((qN W T hπ i y : ↥(NDl W T i)) : W.DD T) = Formalism.MainNotions.LiftingTheory.qp W • (y : W.DD T) := fun y => rfl
  have hpow : ∀ (k : ℕ) (y : ↥(NDl W T i)),
      (((qN W T hπ i ^ k) y : ↥(NDl W T i)) : W.DD T) = Formalism.MainNotions.LiftingTheory.qp W ^ k • (y : W.DD T) := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih => intro y; rw [pow_succ', Module.End.mul_apply, hq1, ih, pow_succ', mul_smul]
  refine ⟨h + η, ?_⟩
  unfold qR
  rw [← Submodule.mapQ_pow]
  ext x
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.zero_comp,
    LinearMap.zero_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  show (((qN W T hπ i ^ (h + η)) x : ↥(NDl W T i)) : W.DD T) ∈ QhP W T i h
  rw [hpow, pow_add, mul_smul]
  unfold QhP
  exact Submodule.mem_map.2 ⟨_, hq x x.2, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩

/- English proof (translation)
Introduce `d T₁ T₂ F b S η m hS i hi`. Take `⟨hfree, hfin⟩` from `h1 d T₁ T₂ F b S η m hS i hi`. Take `⟨m', hm', g, k, he, htor, hrk⟩` from `h3 d T₁ T₂ F b S η m hS i hi`. Unfold `DRData`. Conclude with `⟨m', hm', g, k, hfree, hfin, qR_nil_of W hπ T₂ i (b i + S) η (h2 d T₁ T₂ F b S η m hS i hi), he, htor, hrk⟩`.
-/
theorem drData_of (hπ : W.π₀ ∈ W.AΔ) (h1 : DRFree W) (h2 : DRQEta W) (h3 : DRLat W hπ) :
    ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
      SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
        DRData W T₂ hπ i (b i + S) m (2 * ⌊cD PD.p (hpar n b S + η)⌋₊) (finrank LL T₂.V * S) := by
  intro d T₁ T₂ F b S η m hS i hi
  obtain ⟨hfree, hfin⟩ := h1 d T₁ T₂ F b S η m hS i hi
  obtain ⟨m', hm', g, k, he, htor, hrk⟩ := h3 d T₁ T₂ F b S η m hS i hi
  unfold DRData
  exact ⟨m', hm', g, k, hfree, hfin,
    qR_nil_of W hπ T₂ i (b i + S) η (h2 d T₁ T₂ F b S η m hS i hi), he, htor, hrk⟩

/- English proof (translation)
The claim follows from `LD.lemmaDN_of W (uniformizer_mem_delta_invariants W) hpu (drData_of W (uniformizer_mem_delta_invariants W) h1 h2 h3)`.
-/
theorem lemmaDN_of_pieces (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (h1 : DRFree W) (h2 : DRQEta W)
    (h3 : DRLat W (uniformizer_mem_delta_invariants W)) : LemmaDN W :=
  LD.lemmaDN_of W (uniformizer_mem_delta_invariants W) hpu (drData_of W (uniformizer_mem_delta_invariants W) h1 h2 h3)

/- English proof (translation)
Introduce `d T₁ T₂ F b S η m hS hm i hi x hx`. Take `⟨y, hy, hxy⟩` from `Submodule.mem_map.1 (h0 d T₁ T₂ F b S η m hS hm i hi x hx)`. Rewrite `hxy` using `[LinearMap.smul_apply, LinearMap.id_apply]`. Establish `hπ` using `uniformizer_mem_delta_invariants W`. Establish `hqp` using `qp_mem W hπ`.

Take `⟨X, hX⟩ : ∃ X : LetA O n, X = Formalism.MainNotions.LiftingTheory.qp W - W.π₀` from `⟨_, rfl⟩`. Take `⟨c, hc⟩ : ∃ c : LetA O n, c = ∑ k ∈ Finset.range S, X ^ k * Formalism.MainNotions.LiftingTheory.qp W ^ (S - 1 - k)` from `⟨_, rfl⟩`. Establish `hXeq : X = ((PD.p : ℕ) : LetA O n)`. Rewrite using `[hX]`. Unfold `Formalism.MainNotions.LiftingTheory.qp`.

Expand and normalize the polynomial expressions, which then agree. Establish `hgeom : c * (X - Formalism.MainNotions.LiftingTheory.qp W) = X ^ S - Formalism.MainNotions.LiftingTheory.qp W ^ S`. Rewrite using `[hc]`. Conclude with `geom_sum₂_mul X (Formalism.MainNotions.LiftingTheory.qp W) S`. Establish `hXmem : X ∈ W.AΔ`.

Rewrite using `[hX]`. Conclude with `Subalgebra.sub_mem _ hqp hπ`. Establish `hcmem : c ∈ W.AΔ`. Rewrite using `[hc]`. Conclude with `Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hXmem _) (Subalgebra.pow_mem _ hqp _)`.

Establish `hXq : X - Formalism.MainNotions.LiftingTheory.qp W = -W.π₀`. Rewrite using `[hX]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hgeom` using `[hXq]`. Establish `hX' : X ^ S = W.π₀ * (-c) + Formalism.MainNotions.LiftingTheory.qp W ^ S`.

Take the linear combination `-hgeom`. Establish `hscal : ((PD.p : O) ^ S) • x = (X ^ S) • x`. Rewrite using `[hXeq, ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]`. Rewrite using `[hscal, hX', add_smul, mul_smul]`. Use `Submodule.add_mem_sup ?_ ?_` and prove the remaining obligations.

Conclude with `Submodule.mem_map.2 ⟨(-c) • x, ndl_smul W T₂ i (Subalgebra.neg_mem _ hcmem) hx, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩`. Use `Submodule.mem_map.2 ⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, LinearMap.id_apply, ← hxy, ← mul_smul, ← pow_add, add_comm]`.
-/
theorem lemmaDN0_of_piece (h0 : NinQbP W) : Formalism.MainNotions.N.Pv.LocalLengthBound.LemmaDN0 W := by
  intro d T₁ T₂ F b S η m hS hm i hi x hx
  obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.1 (h0 d T₁ T₂ F b S η m hS hm i hi x hx)
  rw [LinearMap.smul_apply, LinearMap.id_apply] at hxy
  have hπ := uniformizer_mem_delta_invariants W
  have hqp := qp_mem W hπ
  obtain ⟨X, hX⟩ : ∃ X : LetA O n, X = Formalism.MainNotions.LiftingTheory.qp W - W.π₀ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : LetA O n,
      c = ∑ k ∈ Finset.range S, X ^ k * Formalism.MainNotions.LiftingTheory.qp W ^ (S - 1 - k) := ⟨_, rfl⟩
  have hXeq : X = ((PD.p : ℕ) : LetA O n) := by
    rw [hX]
    unfold Formalism.MainNotions.LiftingTheory.qp
    ring
  have hgeom : c * (X - Formalism.MainNotions.LiftingTheory.qp W) = X ^ S - Formalism.MainNotions.LiftingTheory.qp W ^ S := by
    rw [hc]
    exact geom_sum₂_mul X (Formalism.MainNotions.LiftingTheory.qp W) S
  have hXmem : X ∈ W.AΔ := by
    rw [hX]
    exact Subalgebra.sub_mem _ hqp hπ
  have hcmem : c ∈ W.AΔ := by
    rw [hc]
    exact Subalgebra.sum_mem _ fun k _ =>
      Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hXmem _) (Subalgebra.pow_mem _ hqp _)
  have hXq : X - Formalism.MainNotions.LiftingTheory.qp W = -W.π₀ := by
    rw [hX]
    ring
  rw [hXq] at hgeom
  have hX' : X ^ S = W.π₀ * (-c) + Formalism.MainNotions.LiftingTheory.qp W ^ S := by
    linear_combination -hgeom
  have hscal : ((PD.p : O) ^ S) • x = (X ^ S) • x := by
    rw [hXeq, ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [hscal, hX', add_smul, mul_smul]
  refine Submodule.add_mem_sup ?_ ?_
  · exact Submodule.mem_map.2 ⟨(-c) • x, ndl_smul W T₂ i (Subalgebra.neg_mem _ hcmem) hx,
      by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩
  · refine Submodule.mem_map.2 ⟨y, hy, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, ← hxy, ← mul_smul, ← pow_add, add_comm]

def lowSum (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (h η : ℕ) : ℤ :=
  ∑ u ∈ Finset.Icc (-(η : ℤ)) η, multV PD T.ρ τ u * ((h : ℤ) + u)

def DRRank (hπ : W.π₀ ∈ W.AΔ) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d, ∀ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∀ (m' : ℕ) (g : Fin m' → ↥(NDl W T₂ i)) (k : Fin m' → ℕ)
        (_ : ↥(RRp W T₂ hπ i (b i + S) g) ≃ₗ[O] ((j : Fin m') → Aq O (k j))),
        lowSum (PD := PD) T₂ τ (b i + S) η ≤ ∑ j, (k j : ℤ) →
        finrank O (RR W T₂ i (b i + S) ⧸ satL ((PD.p : ℕ) : O) (RRp W T₂ hπ i (b i + S) g)) ≤
          finrank LL T₂.V * S

def WachQuotientCyclicDecomposition (hπ : W.π₀ ∈ W.AΔ) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∃ (m' : ℕ) (_ : m' ≤ m) (g : Fin m' → ↥(NDl W T₂ i)) (k : Fin m' → ℕ),
        (∃ e : ↥(RRp W T₂ hπ i (b i + S) g) ≃ₗ[O] ((j : Fin m') → Aq O (k j)),
          ∀ (x : ↥(RRp W T₂ hπ i (b i + S) g)) (j : Fin m'),
            e ⟨qR W T₂ hπ i (b i + S) x, RRp_stable W T₂ hπ i (b i + S) g x x.2⟩ j =
              Ideal.Quotient.mk _ PowerSeries.X * e x j) ∧
        (∀ (z : RR W T₂ i (b i + S)) (t : ℕ), ((PD.p : ℕ) : O) ^ t • z ∈ RRp W T₂ hπ i (b i + S) g →
          ((PD.p : ℕ) : O) ^ (2 * ⌊cD PD.p (hpar n b S + η)⌋₊) • z ∈ RRp W T₂ hπ i (b i + S) g) ∧
        ∀ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i → lowSum (PD := PD) T₂ τ (b i + S) η ≤ ∑ j, (k j : ℤ)

/- English proof (translation)
Introduce `d T₁ T₂ F b S η m hS i hi`. Take `⟨m', hm', g, k, ⟨e, he⟩, htor, hlow⟩` from `hb d T₁ T₂ F b S η m hS i hi`. Establish `hA : Formalism.MainNotions.LiftingTheory.CaseA W`. Unfold `Formalism.MainNotions.RamifiedCoefficientChains.SetCS at hS`. Conclude with `hS.1`.

Set `eK : K₀ ≃ₐ[Qp] K` to `AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hA.1`. Establish `hov : Formalism.MainNotions.LiftingTheory.Over W ((W.emb i).comp eK.symm.toAlgHom) i`. Unfold `Formalism.MainNotions.LiftingTheory.Over`. Use extensionality with `x`. Use `show W.emb i (eK.symm (IsScalarTower.toAlgHom Qp K₀ K x)) = W.emb i x`.

Establish `hx : IsScalarTower.toAlgHom Qp K₀ K x = eK x` using `rfl`. Rewrite using `[hx, AlgEquiv.symm_apply_apply]`. Conclude with `⟨m', hm', g, k, ⟨e, he⟩, htor, ha d T₁ T₂ F b S η m hS i hi _ hov m' g k e (hlow _ hov)⟩`.
-/
theorem drLat_of (hπ : W.π₀ ∈ W.AΔ) (ha : DRRank W hπ) (hb : WachQuotientCyclicDecomposition W hπ) : DRLat W hπ := by
  intro d T₁ T₂ F b S η m hS i hi
  obtain ⟨m', hm', g, k, ⟨e, he⟩, htor, hlow⟩ := hb d T₁ T₂ F b S η m hS i hi
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := by
    unfold Formalism.MainNotions.RamifiedCoefficientChains.SetCS at hS
    exact hS.1

  let eK : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hA.1
  have hov : Formalism.MainNotions.LiftingTheory.Over W ((W.emb i).comp eK.symm.toAlgHom) i := by
    unfold Formalism.MainNotions.LiftingTheory.Over
    ext x
    show W.emb i (eK.symm (IsScalarTower.toAlgHom Qp K₀ K x)) = W.emb i x
    have hx : IsScalarTower.toAlgHom Qp K₀ K x = eK x := rfl
    rw [hx, AlgEquiv.symm_apply_apply]
  exact ⟨m', hm', g, k, ⟨e, he⟩, htor,
    ha d T₁ T₂ F b S η m hS i hi _ hov m' g k e (hlow _ hov)⟩

/- English proof (translation)
The claim follows from `lemmaDN_of_pieces W hpu h1 h2 (drLat_of W (uniformizer_mem_delta_invariants W) h3a h3b)`.
-/
theorem lemmaDN_of_pieces4 (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (h1 : DRFree W) (h2 : DRQEta W)
    (h3a : DRRank W (uniformizer_mem_delta_invariants W)) (h3b : WachQuotientCyclicDecomposition W (uniformizer_mem_delta_invariants W)) : LemmaDN W :=
  lemmaDN_of_pieces W hpu h1 h2 (drLat_of W (uniformizer_mem_delta_invariants W) h3a h3b)

end Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut
