import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.CrystallineToDeRhamInjective
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvBasisCmp

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

/- English proof (translation)
Simplify using `[cf]`.
-/
theorem cf_sub_level_kernel_detection {Ks D : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (f g : Amb LL Ks D) (i : ℤ) : cf (f - g) i = cf f i - cf g i := by
  simp [cf]

/- English proof (translation)
Simplify using `[cstD, TensorProduct.tmul_add]`.
-/
theorem constSeries_add {Ks D : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (d d' : D) : cstD (LL := LL) Ks (d + d') = cstD Ks d + cstD Ks d' := by
  simp [cstD, TensorProduct.tmul_add]

/- English proof (translation)
Proceed by induction on `(Finset.univ : Finset (Fin q)) using Finset.induction_on with`. Consider the case `empty => simp [cstD]`. Consider the case `insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, constSeries_add, ih]`.
-/
theorem constSeries_sum {Ks D : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    {q : ℕ} (d : Fin q → D) : cstD (LL := LL) Ks (∑ k, d k) = ∑ k, cstD Ks (d k) := by
  classical
  induction (Finset.univ : Finset (Fin q)) using Finset.induction_on with
  | empty => simp [cstD]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, constSeries_add, ih]

/- English proof (translation)
Rewrite using `[HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnModule.single_zero_smul_eq_smul]`. Simplify using `only [cstD]`. Rewrite using `[← HahnModule.of_smul]`. Use `congr 1`. Use extensionality with `j`.

Rewrite using `[HahnSeries.coeff_smul, HahnSeries.coeff_single, HahnSeries.coeff_single]`. Use `split_ifs`. Rewrite using `[algebraMap_smul, TensorProduct.tmul_smul]`. Rewrite using `[smul_zero]`.
-/
theorem constSeries_C_smul {Ks D : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (r : LL) (d : D) :
    HahnSeries.ofPowerSeries ℤ Ks (PowerSeries.C (algebraMap LL Ks r)) • cstD (LL := LL) Ks d =
      cstD Ks (r • d) := by
  rw [HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnModule.single_zero_smul_eq_smul]
  simp only [cstD]
  rw [← HahnModule.of_smul]
  congr 1
  ext j
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs
  · rw [algebraMap_smul, TensorProduct.tmul_smul]
  · rw [smul_zero]

/- English proof (translation)
Simplify using `[cf, cstD, HahnSeries.coeff_single]`.
-/
theorem coeff_constSeries {Ks D : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D] [Module LL D]
    (d : D) (i : ℤ) : cf (cstD (LL := LL) Ks d) i = if i = 0 then (1 : Ks) ⊗ₜ[LL] d else 0 := by
  simp [cf, cstD, HahnSeries.coeff_single]

/- English proof (translation)
Take `⟨u, hu⟩` from `hp9.2.2.2.2.1`. Use `⟨u, ?_⟩` and prove the remaining obligations. Establish `hQq : W.Q = W.q` using `by show (W.φA ^ (W.s - 1)) W.q = W.q`. Rewrite using `[hs1, Nat.sub_self, pow_zero]`. Both sides reduce to the same expression.

Rewrite using `[hQq, hu]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[Formalism.MainNotions.DeltaInvariantLattices.Eat, qP]`.
-/
theorem Q_eq_unit_mul_qP (hs1 : W.s = 1)
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))) :
    ∃ u : (LetA O n)ˣ, W.Q = (u : LetA O n) * qP W := by
  obtain ⟨u, hu⟩ := hp9.2.2.2.2.1
  refine ⟨u, ?_⟩
  have hQq : W.Q = W.q := by
    show (W.φA ^ (W.s - 1)) W.q = W.q
    rw [hs1, Nat.sub_self, pow_zero]
    rfl
  rw [hQq, hu]
  congr 1
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qP]

/- English proof (translation)
Take `⟨w, hw⟩` from `hp9.2.2.1`. Establish `hp1 : PD.p - 1 ≠ 0` using `by have := PD.hp.two_le; omega`. Rewrite using `[hw]`. Simplify using `[letπ, zero_pow hp1]`.
-/
theorem constantCoeff_pi0_eq_zero_of_p9ring
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (j : ZMod n) : PowerSeries.constantCoeff (W.π₀ j) = 0 := by
  obtain ⟨w, hw⟩ := hp9.2.2.1
  have hp1 : PD.p - 1 ≠ 0 := by have := PD.hp.two_le; omega
  rw [hw]
  simp [letπ, zero_pow hp1]

def comparisonOnLetter {T : LocLat G Qp LL O} (C : Coord W (baseIdOf hR) T) (i : ZMod n) :
    ↥((latOf C).N i) →+ T.V ⊗[Qp] B where
  toFun y := W.cmp T ⟨C.t i y, y.2⟩
  map_zero' := by
    rw [← map_zero (W.cmp T)]
    exact lvBasis_cmp_congr _ _ (C.t_zero i)
  map_add' y y' := by
    rw [← lvBasis_cmp_add y.2 y'.2 ((W.N T).add_mem y.2 y'.2)]
    exact lvBasis_cmp_congr _ _ (C.t_add i _ _)

/- English proof (translation)
Take `⟨z, hz, hzeq⟩` from `Submodule.mem_map.1 hred`. Rewrite `hzeq` using `[LinearMap.lsmul_apply]`. Establish `key : (⟨x, hx⟩ : ↥((latOf C).N i)) = ∑ k, PowerSeries.C (a k) • (⟨e k, he k⟩ : ↥((latOf C).N i)) + (PowerSeries.X : PowerSeries O) • ⟨z, hz⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul]`.

Rewrite using `[hzeq]`. Normalize the expressions using the abelian group laws. Establish `hF` using `congrArg (comparisonOnLetter C i) key`. Rewrite `hF` using `[map_add, map_sum]`. Establish `hC : ∀ k, comparisonOnLetter C i (PowerSeries.C (a k) • (⟨e k, he k⟩ : ↥((latOf C).N i))) = algebraMap O LL (a k) • W.cmp T ⟨C.t i (e k), he k⟩`.

Introduce `k`. Establish `hm : (baseIdOf hR).d (PowerSeries.C (a k)) • C.t i (e k) ∈ W.N T`. Rewrite using `[← C.t_smul]`. Conclude with `(PowerSeries.C (a k) • (⟨e k, he k⟩ : ↥((latOf C).N i))).2`. Establish `h0 : comparisonOnLetter C i (PowerSeries.C (a k) • (⟨e k, he k⟩ : ↥((latOf C).N i))) = W.cmp T ⟨(baseIdOf hR).d (PowerSeries.C (a k)) • C.t i (e k), hm⟩` using `lvBasis_cmp_congr (a := C.t i (PowerSeries.C (a k) • e k)) (PowerSeries.C (a k) • (⟨e k, he k⟩ : ↥((latOf C).N i))).2 hm (C.t_smul i _ _)`.

Rewrite using `[h0]`. Use `lvBasis_cmp_smul_const (he k) _ (a k) (fun j => ?_) hm` and prove the remaining obligations. Rewrite using `[BaseId.d_apply]`. Establish `h1 : (baseIdOf hR).ι (PowerSeries.C (a k)) = PowerSeries.C (a k)` using `(baseIdOf hR).ι.commutes (a k)`. Rewrite using `[h1, PowerSeries.constantCoeff_C]`.

Establish `hX : comparisonOnLetter C i ((PowerSeries.X : PowerSeries O) • (⟨z, hz⟩ : ↥((latOf C).N i))) = 0`. Establish `hm : W.π₀ • C.t i z ∈ W.N T`. Rewrite using `[← BaseId.d_X, ← C.t_smul]`. Conclude with `((PowerSeries.X : PowerSeries O) • (⟨z, hz⟩ : ↥((latOf C).N i))).2`. Establish `h0 : comparisonOnLetter C i ((PowerSeries.X : PowerSeries O) • (⟨z, hz⟩ : ↥((latOf C).N i))) = W.cmp T ⟨W.π₀ • C.t i z, hm⟩` using `lvBasis_cmp_congr (a := C.t i ((PowerSeries.X : PowerSeries O) • z)) ((PowerSeries.X : PowerSeries O) • (⟨z, hz⟩ : ↥((latOf C).N i))).2 hm (by rw [C.t_smul, BaseId.d_X])`.

Rewrite using `[h0, lvBasis_cmp_smul_const hz W.π₀ 0 (constantCoeff_pi0_eq_zero_of_p9ring hp9) hm, map_zero, zero_smul]`. Rewrite `hF` using `[hX, add_zero, Finset.sum_congr rfl (fun k _ => hC k)]`. Conclude with `hF`.
-/
theorem comparison_of_reduction {T : LocLat G Qp LL O} (C : Coord W (baseIdOf hR) T) (i : ZMod n)
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    {r : ℕ} (e : Fin r → C.V) (he : ∀ k, e k ∈ (latOf C).N i) (x : C.V) (hx : x ∈ (latOf C).N i)
    (a : Fin r → O) (hred : x - ∑ k, PowerSeries.C (a k) • e k ∈ E.sm (PowerSeries.X : PowerSeries O) ((latOf C).N i)) :
    W.cmp T ⟨C.t i x, hx⟩ = ∑ k, algebraMap O LL (a k) • W.cmp T ⟨C.t i (e k), he k⟩ := by
  obtain ⟨z, hz, hzeq⟩ := Submodule.mem_map.1 hred
  rw [LinearMap.lsmul_apply] at hzeq
  have key : (⟨x, hx⟩ : ↥((latOf C).N i)) =
      ∑ k, PowerSeries.C (a k) • (⟨e k, he k⟩ : ↥((latOf C).N i)) + (PowerSeries.X : PowerSeries O) • ⟨z, hz⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul]
    rw [hzeq]
    abel
  have hF := congrArg (comparisonOnLetter C i) key
  rw [map_add, map_sum] at hF
  have hC : ∀ k, comparisonOnLetter C i (PowerSeries.C (a k) • (⟨e k, he k⟩ : ↥((latOf C).N i))) =
      algebraMap O LL (a k) • W.cmp T ⟨C.t i (e k), he k⟩ := by
    intro k
    have hm : (baseIdOf hR).d (PowerSeries.C (a k)) • C.t i (e k) ∈ W.N T := by
      rw [← C.t_smul]
      exact (PowerSeries.C (a k) • (⟨e k, he k⟩ : ↥((latOf C).N i))).2
    have h0 : comparisonOnLetter C i (PowerSeries.C (a k) • (⟨e k, he k⟩ : ↥((latOf C).N i))) =
        W.cmp T ⟨(baseIdOf hR).d (PowerSeries.C (a k)) • C.t i (e k), hm⟩ :=
      lvBasis_cmp_congr (a := C.t i (PowerSeries.C (a k) • e k))
        (PowerSeries.C (a k) • (⟨e k, he k⟩ : ↥((latOf C).N i))).2 hm (C.t_smul i _ _)
    rw [h0]
    refine lvBasis_cmp_smul_const (he k) _ (a k) (fun j => ?_) hm
    rw [BaseId.d_apply]
    have h1 : (baseIdOf hR).ι (PowerSeries.C (a k)) = PowerSeries.C (a k) :=
      (baseIdOf hR).ι.commutes (a k)
    rw [h1, PowerSeries.constantCoeff_C]
  have hX : comparisonOnLetter C i ((PowerSeries.X : PowerSeries O) • (⟨z, hz⟩ : ↥((latOf C).N i))) = 0 := by
    have hm : W.π₀ • C.t i z ∈ W.N T := by
      rw [← BaseId.d_X, ← C.t_smul]
      exact ((PowerSeries.X : PowerSeries O) • (⟨z, hz⟩ : ↥((latOf C).N i))).2
    have h0 : comparisonOnLetter C i ((PowerSeries.X : PowerSeries O) • (⟨z, hz⟩ : ↥((latOf C).N i))) =
        W.cmp T ⟨W.π₀ • C.t i z, hm⟩ :=
      lvBasis_cmp_congr (a := C.t i ((PowerSeries.X : PowerSeries O) • z))
        ((PowerSeries.X : PowerSeries O) • (⟨z, hz⟩ : ↥((latOf C).N i))).2 hm
        (by rw [C.t_smul, BaseId.d_X])
    rw [h0, lvBasis_cmp_smul_const hz W.π₀ 0 (constantCoeff_pi0_eq_zero_of_p9ring hp9) hm, map_zero, zero_smul]
  rw [hX, add_zero, Finset.sum_congr rfl (fun k _ => hC k)] at hF
  exact hF

/- English proof (translation)
Take `⟨z, hz, hzeq⟩` from `Submodule.mem_map.1 hγ`. Rewrite `hzeq` using `[LinearMap.lsmul_apply]`. Establish `hg : W.gamK = W.gam` using `W.gamK_eq_one hs1 hp2`. Establish `h1 : C.t i ((latOf C).γ i x) = W.γD T W.gam (C.t i x)` using `by rw [t_γ, hg]`. Establish `h2 : W.γD T W.gam (C.t i x) - C.t i x = W.π₀ ^ M • C.t i z`.

Rewrite using `[← h1, ← C.t_sub, ← hzeq, C.t_smul, map_pow, BaseId.d_X]`. Use `⟨⟨C.t i z, hz⟩, ?_, h2⟩` and prove the remaining obligations. Establish `h3 : W.γD T W.gam (C.t i x) = W.π₀ ^ M • C.t i z + C.t i x` using `by rw [← h2]; abel`. Rewrite using `[h3]`. Conclude with `(W.N T).add_mem ((W.N T).smul_mem _ hz) hx`.
-/
theorem gamma_reduction_pi0_pow {T : LocLat G Qp LL O} (C : Coord W (baseIdOf hR) T) (i : ZMod n) (hs1 : W.s = 1)
    (hp2 : PD.p ≠ 2) (x : C.V) (hx : x ∈ (latOf C).N i) (M : ℕ)
    (hγ : (latOf C).γ i x - x ∈ E.sm ((PowerSeries.X : PowerSeries O) ^ M) ((latOf C).N i)) :
    ∃ (y : ↥(W.N T)) (_ : W.γD T W.gam (C.t i x) ∈ W.N T),
      W.γD T W.gam (C.t i x) - C.t i x = W.π₀ ^ M • (y : W.DD T) := by
  obtain ⟨z, hz, hzeq⟩ := Submodule.mem_map.1 hγ
  rw [LinearMap.lsmul_apply] at hzeq
  have hg : W.gamK = W.gam := W.gamK_eq_one hs1 hp2
  have h1 : C.t i ((latOf C).γ i x) = W.γD T W.gam (C.t i x) := by rw [t_γ, hg]
  have h2 : W.γD T W.gam (C.t i x) - C.t i x = W.π₀ ^ M • C.t i z := by
    rw [← h1, ← C.t_sub, ← hzeq, C.t_smul, map_pow, BaseId.d_X]
  refine ⟨⟨C.t i z, hz⟩, ?_, h2⟩
  have h3 : W.γD T W.gam (C.t i x) = W.π₀ ^ M • C.t i z + C.t i x := by rw [← h2]; abel
  rw [h3]
  exact (W.N T).add_mem ((W.N T).smul_mem _ hz) hx

end Formalism.MainNotions.N.Ln03.Pf
