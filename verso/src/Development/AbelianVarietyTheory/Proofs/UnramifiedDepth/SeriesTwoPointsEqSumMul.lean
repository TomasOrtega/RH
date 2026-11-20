import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesEvalOfPowMem

namespace GlobalTheory

namespace SeriesTensor

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx i`. Establish `hle : (I • ⊤ : Submodule R M) ≤ Submodule.comap (b.coord i) I` using `Submodule.smul_le.2 fun r hr m _ => by`. Rewrite using `[Submodule.mem_comap, map_smul, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ hr`.

Conclude with `hle hx`. Introduce `h`. Rewrite using `[← b.sum_repr x]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top`.
-/
private theorem mem_smul_top_iff {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ (I • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    have hle : (I • ⊤ : Submodule R M) ≤ Submodule.comap (b.coord i) I :=
      Submodule.smul_le.2 fun r hr m _ => by
        rw [Submodule.mem_comap, map_smul, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
    exact hle hx
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

/- English proof (translation)
Establish `htop : ∀ k : ℕ, (I ^ k • ⊤ : Submodule R R) = I ^ k` using `fun k => by`. Rewrite using `[smul_eq_mul, Ideal.mul_top]`. Establish `hH : IsHausdorff I M`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Use `b.repr.injective (Finsupp.ext fun i => ?_)` and prove the remaining obligations.

Rewrite using `[map_zero, Finsupp.zero_apply]`. Use `IsHausdorff.haus' (I := I) _ fun n => ?_` and prove the remaining obligations. Use `hx n` as an intermediate fact. Rewrite `this` using `[SModEq.zero, mem_smul_top_iff b]`. Rewrite using `[SModEq.zero, htop]`.

Conclude with `this i`. Establish `hP' : IsPrecomplete I M`. Rewrite using `[isPrecomplete_iff]`. Introduce `F hF`. Establish `hP` using `hI.toIsPrecomplete`.

Rewrite `hP` using `[isPrecomplete_iff]`. Establish `hc : ∀ i, ∃ L : R, ∀ k, b.repr (F k) i ≡ L [SMOD (I ^ k • ⊤ : Submodule R R)]`. Introduce `i`. Use `hP (fun k => b.repr (F k) i) fun {m n} hmn => ?_` and prove the remaining obligations. Use `hF hmn` as an intermediate fact.

Rewrite `this` using `[SModEq.sub_mem, mem_smul_top_iff b]`. Rewrite using `[SModEq.sub_mem, htop]`. Simplify using `using this i`. Use `choose L hL using hc`. Use `⟨∑ i, L i • b i, fun k => ?_⟩` and prove the remaining obligations.

Rewrite using `[SModEq.sub_mem, mem_smul_top_iff b]`. Introduce `i`. Use `hL i k` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, htop]`. Establish `hr : b.repr (∑ j, L j • b j) i = L i`.

Establish `h` using `congrFun (b.equivFun.apply_symm_apply L) i`. Rewrite `h` using `[Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply]`. Then use the resulting hypothesis. Rewrite using `[map_sub, Finsupp.sub_apply, hr]`. Conclude with `this`. Conclude with `{ toIsHausdorff := hH, toIsPrecomplete := hP' }`.
-/
private theorem isAdicComplete_of_basis {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) [hI : IsAdicComplete I R] :
    IsAdicComplete I M := by
  have htop : ∀ k : ℕ, (I ^ k • ⊤ : Submodule R R) = I ^ k := fun k => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus' (I := I) _ fun n => ?_
    have := hx n
    rw [SModEq.zero, mem_smul_top_iff b] at this
    rw [SModEq.zero, htop]
    exact this i
  have hP' : IsPrecomplete I M := by
    rw [isPrecomplete_iff]
    intro F hF
    have hP := hI.toIsPrecomplete
    rw [isPrecomplete_iff] at hP
    have hc : ∀ i, ∃ L : R, ∀ k, b.repr (F k) i ≡ L [SMOD (I ^ k • ⊤ : Submodule R R)] := by
      intro i
      refine hP (fun k => b.repr (F k) i) fun {m n} hmn => ?_
      have := hF hmn
      rw [SModEq.sub_mem, mem_smul_top_iff b] at this
      rw [SModEq.sub_mem, htop]
      simpa using this i
    choose L hL using hc
    refine ⟨∑ i, L i • b i, fun k => ?_⟩
    rw [SModEq.sub_mem, mem_smul_top_iff b]
    intro i
    have := hL i k
    rw [SModEq.sub_mem, htop] at this
    have hr : b.repr (∑ j, L j • b j) i = L i := by
      have h := congrFun (b.equivFun.apply_symm_apply L) i
      rwa [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply] at h
    rw [map_sub, Finsupp.sub_apply, hr]
    exact this
  exact { toIsHausdorff := hH, toIsPrecomplete := hP' }

/- English proof (translation)
Establish `h1 : v (algebraMap O C c) < 1` using `lt_of_le_of_ne (hv.map_le_one c) fun h => hc (hv.isUnit_iff_valuation_eq_one.2 h)`. Establish `h0 : 0 < v (algebraMap O C a)` using `pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 ha)`. Take `⟨n, hn⟩` from `NNReal.exists_pow_lt_of_lt_one h0 h1`. Use `⟨n, Ideal.mem_span_singleton.2 (hv.dvd_of_le ?_)⟩` and prove the remaining obligations. Rewrite using `[map_pow, map_pow]`.

Conclude with `hn.le`.
-/
private theorem exists_pow_mem {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) {a c : O} (ha : algebraMap O C a ≠ 0) (hc : ¬ IsUnit c) :
    ∃ n : ℕ, c ^ n ∈ Ideal.span {a} := by
  have h1 : v (algebraMap O C c) < 1 :=
    lt_of_le_of_ne (hv.map_le_one c) fun h => hc (hv.isUnit_iff_valuation_eq_one.2 h)
  have h0 : 0 < v (algebraMap O C a) := pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 ha)
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one h0 h1
  refine ⟨n, Ideal.mem_span_singleton.2 (hv.dvd_of_le ?_)⟩
  rw [map_pow, map_pow]
  exact hn.le

/- English proof (translation)
Express the relevant statement in the definitionally equal form `π (MvPowerSeries.X j) ∈ (I.map (algebraMap O A)).radical`. Rewrite using `[Ideal.radical_eq_sInf, Submodule.mem_sInf]`. Introduce and unpack `(P : Ideal A) ⟨hIP, hP⟩`. Establish `hmax : (Ideal.comap (algebraMap O A) P).IsMaximal`. Establish `hle : IsLocalRing.maximalIdeal O ≤ Ideal.comap (algebraMap O A) P`.

Introduce `c hc`. Take `⟨n, hn⟩` from `hI c hc`. Establish `: c ^ n ∈ Ideal.comap (algebraMap O A) P` using `(Ideal.map_le_iff_le_comap.1 hIP) hn`. Conclude with `(Ideal.comap_isPrime _ P).mem_of_pow_mem n this`. Use `(IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_isPrime _ P).ne_top hle` as an intermediate fact.

Rewrite using `[← this]`. Conclude with `IsLocalRing.maximalIdeal.isMaximal O`. Establish `hPm : P.IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hmax`. Establish `h2 : (Ideal.comap (π : MvPowerSeries σ O →+* A) P).IsMaximal` using `Ideal.comap_isMaximal_of_surjective (π : MvPowerSeries σ O →+* A) hπ`. Establish `h3` using `IsLocalRing.eq_maximalIdeal h2`.

Establish `h4 : (MvPowerSeries.X j : MvPowerSeries σ O) ∈ IsLocalRing.maximalIdeal _`. Introduce `hu`. Rewrite `hu` using `[MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X]`. Conclude with `not_isUnit_zero hu`. Rewrite `h4` using `[← h3]`.

Conclude with `h4`.
-/
private theorem exists_pow_X_mem {O σ A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [Algebra O A] [Algebra.IsIntegral O A] (I : Ideal O)
    (hI : ∀ c : O, ¬ IsUnit c → ∃ n : ℕ, c ^ n ∈ I) (π : MvPowerSeries σ O →ₐ[O] A)
    (hπ : Function.Surjective π) (j : σ) :
    ∃ M : ℕ, π (MvPowerSeries.X j) ^ M ∈ I.map (algebraMap O A) := by
  change π (MvPowerSeries.X j) ∈ (I.map (algebraMap O A)).radical
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro (P : Ideal A) ⟨hIP, hP⟩
  have hmax : (Ideal.comap (algebraMap O A) P).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal O ≤ Ideal.comap (algebraMap O A) P := by
      intro c hc
      obtain ⟨n, hn⟩ := hI c hc
      have : c ^ n ∈ Ideal.comap (algebraMap O A) P := (Ideal.map_le_iff_le_comap.1 hIP) hn
      exact (Ideal.comap_isPrime _ P).mem_of_pow_mem n this
    have := (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_isPrime _ P).ne_top hle
    rw [← this]
    exact IsLocalRing.maximalIdeal.isMaximal O
  have hPm : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hmax
  have h2 : (Ideal.comap (π : MvPowerSeries σ O →+* A) P).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (π : MvPowerSeries σ O →+* A) hπ
  have h3 := IsLocalRing.eq_maximalIdeal h2
  have h4 : (MvPowerSeries.X j : MvPowerSeries σ O) ∈ IsLocalRing.maximalIdeal _ := by
    intro hu
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at hu
    exact not_isUnit_zero hu
  rw [← h3] at h4
  exact h4

/- English proof (translation)
Take `⟨M, hM⟩` from `h`. Use `⟨M, ?_⟩` and prove the remaining obligations. Use `Ideal.mem_map_of_mem (e : A →+* B) hM` as an intermediate fact. Rewrite `this` using `[Ideal.map_map, AlgHom.comp_algebraMap, map_pow]`. Conclude with `this`.
-/
private theorem pow_mem_map {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
    [Algebra O B] (I : Ideal O) (e : A →ₐ[O] B) {x : A}
    (h : ∃ M : ℕ, x ^ M ∈ I.map (algebraMap O A)) :
    ∃ M : ℕ, e x ^ M ∈ I.map (algebraMap O B) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, ?_⟩
  have := Ideal.mem_map_of_mem (e : A →+* B) hM
  rw [Ideal.map_map, AlgHom.comp_algebraMap, map_pow] at this
  exact this

end SeriesTensor

end GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Unfold `ev`. Rewrite using `[MvPowerSeries.subst_X]`. Both sides reduce to the same expression. Use `MvPowerSeries.hasSubst_of_constantCoeff_zero ?_` and prove the remaining obligations. Introduce and unpack `⟨a, l⟩`.

Use `fin_cases a`. Conclude with `MvPowerSeries.constantCoeff_X _`.
-/
private theorem SeriesTensor.ev_pt_X {R : Type} [CommRing R] {d : ℕ} (k : Fin 2) (i : Fin d) :
    ev (n := 2) ![pt R d k] (MvPowerSeries.X ((0 : Fin 1), i)) = MvPowerSeries.X (k, i) := by
  unfold ev
  rw [MvPowerSeries.subst_X]
  · rfl
  · refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
    rintro ⟨a, l⟩
    fin_cases a
    exact MvPowerSeries.constantCoeff_X _

open SeriesTensor in

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ hv _ _ d J hfree hfin f`. Establish `hdom : IsDomain O` using `hv.hom_inj.isDomain _`. Use `ValuationRing.of_integers v hv` as an intermediate fact. Use `set I : Ideal O := Ideal.span {(p : O)}`. Establish `hp0 : algebraMap O C (p : O) ≠ 0`.

Rewrite using `[map_natCast]`. Conclude with `Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero`. Establish `hI : ∀ c : O, ¬ IsUnit c → ∃ n : ℕ, c ^ n ∈ I` using `fun c hc => exists_pow_mem hv hp0 hc`. Set `Q` to `PS O 1 d ⧸ J`. Set `π : PS O 1 d →ₐ[O] Q` to `Ideal.Quotient.mkₐ O J`.

Establish `hπ : Function.Surjective π` using `Ideal.Quotient.mkₐ_surjective O J`. Set `A` to `Q ⊗[O] Q`. Establish `hA : IsAdicComplete (I.map (algebraMap O A)) A`. Rewrite using `[IsAdicComplete.map_algebraMap_iff]`. Conclude with `isAdicComplete_of_basis (Module.Free.chooseBasis O A) I`.

Set `e : Fin 2 → (Q →ₐ[O] A)` to `![Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight]`. Set `a : Fin 2 × Fin d → A` to `fun q => e q.1 (π (MvPowerSeries.X (0, q.2)))`. Establish `ha : ∀ q, ∃ M : ℕ, a q ^ M ∈ I.map (algebraMap O A)` using `fun q => pow_mem_map (A := Q) (B := A) I (e q.1) (exists_pow_X_mem (A := Q) I hI π hπ (0, q.2))`. Take `⟨Ψ, hΨ⟩` from `(mvPowerSeries_eval_of_pow_mem A _ _ a ha).1 hA O`. Take `⟨m, x, y, hxy⟩` from `TensorProduct.exists_sum_tmul_eq (Ψ f)`.

Use `choose g hg using fun i => hπ (x i)`. Use `choose h hh using fun i => hπ (y i)`. Use `⟨m, g, h, fun Φ φ φ' h0 h1 hJ hJ' => ?_⟩` and prove the remaining obligations. Set `ψ : Q →ₐ[O] O` to `Ideal.Quotient.liftₐ J φ hJ`. Set `ψ' : Q →ₐ[O] O` to `Ideal.Quotient.liftₐ J φ' hJ'`.

Set `T : A →ₐ[O] O` to `Algebra.TensorProduct.lift ψ ψ' fun _ _ => Commute.all _ _`. Establish `hsurj : Function.Surjective Φ` using `fun c => ⟨algebraMap O _ c, Φ.commutes c⟩`. Establish `hnil` using `fun q => exists_pow_X_mem I hI Φ hsurj q`. Establish `hH : IsHausdorff (I.map (algebraMap O O)) O`. Rewrite using `[IsHausdorff.map_algebraMap_iff]`.

Use `infer_instance`. Establish `key` using `(mvPowerSeries_eval_of_pow_mem O _ _ _ hnil).2 hH O (Φ : PS O 2 d →+* O) (T.comp Ψ : PS O 2 d →+* O) (fun t => (Φ.commutes t).trans ((T.comp Ψ).commutes t).symm) (fun _ => rfl) (by`. Introduce and unpack `⟨k, i⟩`. Express the relevant statement in the definitionally equal form `T (Ψ (MvPowerSeries.X (k, i))) = _`. Rewrite using `[hΨ, ← ev_pt_X k i]`.

Use `fin_cases k`. Use `Eq.trans ?_ (h0 _).symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `T (π _ ⊗ₜ 1) = _`. Rewrite using `[Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]`. Both sides reduce to the same expression.

Use `Eq.trans ?_ (h1 _).symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `T (1 ⊗ₜ π _) = _`. Rewrite using `[Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]`. Use the proof step `rfl)`. Establish `hf : Φ f = T (Ψ f)` using `RingHom.congr_fun key f`.

Rewrite using `[hf, hxy, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hg, ← hh]`. Conclude with `Algebra.TensorProduct.lift_tmul _ _ _ _ _`.
-/
theorem series_two_points_eq_sum_mul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (J : Ideal (PS O 1 d)), Module.Free O (PS O 1 d ⧸ J) → Module.Finite O (PS O 1 d ⧸ J) → ∀ f : PS O 2 d, ∃ (m : ℕ) (g h : Fin m → PS O 1 d), ∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O), (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) → (∀ u ∈ J, φ u = 0) → (∀ u ∈ J, φ' u = 0) → Φ f = ∑ i, φ (g i) * φ' (h i) := by
  intro p _ C _ _ _ v O _ _ hv _ _ d J hfree hfin f
  have hdom : IsDomain O := hv.hom_inj.isDomain _
  have := ValuationRing.of_integers v hv
  set I : Ideal O := Ideal.span {(p : O)}
  have hp0 : algebraMap O C (p : O) ≠ 0 := by
    rw [map_natCast]
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hI : ∀ c : O, ¬ IsUnit c → ∃ n : ℕ, c ^ n ∈ I := fun c hc => exists_pow_mem hv hp0 hc
  let Q := PS O 1 d ⧸ J
  let π : PS O 1 d →ₐ[O] Q := Ideal.Quotient.mkₐ O J
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective O J
  let A := Q ⊗[O] Q
  have hA : IsAdicComplete (I.map (algebraMap O A)) A := by
    rw [IsAdicComplete.map_algebraMap_iff]
    exact isAdicComplete_of_basis (Module.Free.chooseBasis O A) I
  let e : Fin 2 → (Q →ₐ[O] A) :=
    ![Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight]
  let a : Fin 2 × Fin d → A := fun q => e q.1 (π (MvPowerSeries.X (0, q.2)))
  have ha : ∀ q, ∃ M : ℕ, a q ^ M ∈ I.map (algebraMap O A) := fun q =>
    pow_mem_map (A := Q) (B := A) I (e q.1) (exists_pow_X_mem (A := Q) I hI π hπ (0, q.2))
  obtain ⟨Ψ, hΨ⟩ := (mvPowerSeries_eval_of_pow_mem A _ _ a ha).1 hA O
  obtain ⟨m, x, y, hxy⟩ := TensorProduct.exists_sum_tmul_eq (Ψ f)
  choose g hg using fun i => hπ (x i)
  choose h hh using fun i => hπ (y i)
  refine ⟨m, g, h, fun Φ φ φ' h0 h1 hJ hJ' => ?_⟩
  let ψ : Q →ₐ[O] O := Ideal.Quotient.liftₐ J φ hJ
  let ψ' : Q →ₐ[O] O := Ideal.Quotient.liftₐ J φ' hJ'
  let T : A →ₐ[O] O := Algebra.TensorProduct.lift ψ ψ' fun _ _ => Commute.all _ _
  have hsurj : Function.Surjective Φ := fun c => ⟨algebraMap O _ c, Φ.commutes c⟩
  have hnil := fun q => exists_pow_X_mem I hI Φ hsurj q
  have hH : IsHausdorff (I.map (algebraMap O O)) O := by
    rw [IsHausdorff.map_algebraMap_iff]
    infer_instance
  have key := (mvPowerSeries_eval_of_pow_mem O _ _ _ hnil).2 hH O
    (Φ : PS O 2 d →+* O) (T.comp Ψ : PS O 2 d →+* O)
    (fun t => (Φ.commutes t).trans ((T.comp Ψ).commutes t).symm) (fun _ => rfl) (by
      rintro ⟨k, i⟩
      change T (Ψ (MvPowerSeries.X (k, i))) = _
      rw [hΨ, ← ev_pt_X k i]
      fin_cases k
      · refine Eq.trans ?_ (h0 _).symm
        change T (π _ ⊗ₜ 1) = _
        rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
        rfl
      · refine Eq.trans ?_ (h1 _).symm
        change T (1 ⊗ₜ π _) = _
        rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
        rfl)
  have hf : Φ f = T (Ψ f) := RingHom.congr_fun key f
  rw [hf, hxy, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hg, ← hh]
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

end GlobalTheory
