import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointOperatorIdentities
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsFFNeZeroThree

open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities

noncomputable section
namespace GlobalTheory.PairOp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_ofDual (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (c : 𝓀[k]ˣ)
    (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) :
    c • ofDual L f = ofDual L ⟨(c : 𝓀[k]) • f.1, smul_ne_zero c.ne_zero f.2⟩ := rfl

/- English proof (translation)
Take `⟨s, hs⟩` from `IsLocalRing.residue_surjective (((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k]))`. Establish `hy : Red.mk L x.1.out = x.1` using `Red.mk_out x.1`. Establish `h1 : (up L q x).HasVal (q.inv • ((x.1.out : L) : n → k)) 1` using `(up_hasVal_iff L q x _).mpr hy`. Establish `h2` using `Pair.dia_hasVal_one (c := c) h1 hs`. Establish `h3 : (up L q ⟨((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) • x.1, smul_ne_zero (c⁻¹).ne_zero x.2⟩).HasVal (q.inv • ((s • x.1.out : L) : n → k)) 1`.

Rewrite using `[up_hasVal_iff, map_smul, hy]`. Use `show s • x.1 = ((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) • x.1`. Rewrite using `[← hs, Red.residue_smul]`. Rewrite `h3` using `[Submodule.coe_smul, smul_comm]`. Conclude with `Pair.ext_ker (by rw [Pair.dia_ker, up_ker, up_ker]) h2 h3`.
-/
theorem smul_up (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (q : Unif k) (c : 𝓀[k]ˣ) (x : {x : Red L // x ≠ 0}) :
    c • up L q x = up L q ⟨((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) • x.1, smul_ne_zero (c⁻¹).ne_zero x.2⟩ := by
  obtain ⟨s, hs⟩ := IsLocalRing.residue_surjective (((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k]))
  have hy : Red.mk L x.1.out = x.1 := Red.mk_out x.1
  have h1 : (up L q x).HasVal (q.inv • ((x.1.out : L) : n → k)) 1 := (up_hasVal_iff L q x _).mpr hy
  have h2 := Pair.dia_hasVal_one (c := c) h1 hs
  have h3 : (up L q ⟨((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) • x.1, smul_ne_zero (c⁻¹).ne_zero x.2⟩).HasVal
      (q.inv • ((s • x.1.out : L) : n → k)) 1 := by
    rw [up_hasVal_iff, map_smul, hy]
    show s • x.1 = ((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) • x.1
    rw [← hs, Red.residue_smul]
  rw [Submodule.coe_smul, smul_comm] at h3
  exact Pair.ext_ker (by rw [Pair.dia_ker, up_ker, up_ker]) h2 h3

/- English proof (translation)
Rewrite using `[← Finset.sum_image (fun i _ j _ hij => he hij)]`. Use `Model.sum_stable_eq_zero h _ fun c P => ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `hP`. Take `⟨i, hi, hPi⟩` from `Finset.mem_image.mp hP`.

Take `⟨j, hj, hj'⟩` from `hS c⁻¹ i hi`. Use `Finset.mem_image.mpr ⟨j, hj, ?_⟩` and prove the remaining obligations. Rewrite using `[hj', hPi, inv_smul_smul]`. Introduce `hP`. Take `⟨i, hi, rfl⟩` from `Finset.mem_image.mp hP`.

Take `⟨j, hj, hj'⟩` from `hS c i hi`. Conclude with `Finset.mem_image.mpr ⟨j, hj, hj'⟩`.
-/
theorem sum_family_eq_zero {ι : Type} {φ : Form k n M} (h : φ ∈ Mram k n M) (e : ι → Pair k n)
    (he : Function.Injective e) (S : Finset ι) (hS : ∀ (c : 𝓀[k]ˣ), ∀ i ∈ S, ∃ j ∈ S, e j = c • e i) :
    ∑ i ∈ S, φ (e i) = 0 := by
  classical
  rw [← Finset.sum_image (fun i _ j _ hij => he hij)]
  refine Model.sum_stable_eq_zero h _ fun c P => ?_
  constructor
  · intro hP
    obtain ⟨i, hi, hPi⟩ := Finset.mem_image.mp hP
    obtain ⟨j, hj, hj'⟩ := hS c⁻¹ i hi
    refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
    rw [hj', hPi, inv_smul_smul]
  · intro hP
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨j, hj, hj'⟩ := hS c i hi
    exact Finset.mem_image.mpr ⟨j, hj, hj'⟩

/- English proof (translation)
Rewrite using `[trLat_apply]`. Conclude with `Model.sum_stable_eq_zero h _ fun c P => by simp`. Use `trKer_eq_zero φ h L _ := by`. Rewrite using `[trKer_apply]`. Conclude with `Model.sum_stable_eq_zero h _ fun c P => by simp`.

Use `partial_lat φ h L _ S hS := by`. Use `sum_family_eq_zero h (fun f => ofDual L f) (fun f g hfg => ?_) S fun c f hf => ?_` and prove the remaining obligations. Conclude with `(latEquiv L).injective (Subtype.ext hfg)`. Conclude with `⟨⟨(c : 𝓀[k]) • f.1, smul_ne_zero c.ne_zero f.2⟩, hS c f _ hf rfl, (smul_ofDual L c f).symm⟩`. Use `partial_ker φ h L _ S hS := by`.

Use `sum_family_eq_zero h (fun x => up L q x) (fun x y hxy => ?_) S fun c x hx => ?_` and prove the remaining obligations. Conclude with `(kerEquiv L q).injective (Subtype.ext hxy)`. Conclude with `⟨⟨((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) • x.1, smul_ne_zero (c⁻¹).ne_zero x.2⟩, hS c⁻¹ x _ hx rfl, (smul_up L q c x).symm⟩`. Use `invariant_eq_zero π P v hv M' _ _ θ hθ := by classical`. Use `letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _`.

Establish `scal : ∀ s : 𝒪[k]ˣ, ∃ g : GL n k, ∀ x : n → k, g • x = (s : 𝒪[k]) • x`. Introduce `s`. Use `⟨Units.map (Matrix.scalar n : k →+* Matrix n n k).toMonoidHom (Units.map (algebraMap 𝒪[k] k).toMonoidHom s), fun x => ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Simplify using `[Units.smul_def, Matrix.scalar_apply, Matrix.mulVec_diagonal, Algebra.smul_def]`.

Establish `stab : ∀ (g : GL n k) (s : 𝒪[k]ˣ), (∀ x : n → k, g • x = (s : 𝒪[k]) • x) → ∀ L : Submodule 𝒪[k] (n → k), g ∈ latStab L`. Introduce `g s hg L`. Use `open Pointwise in rw [MulAction.mem_stabilizer_iff]`. Use extensionality with `x`. Rewrite using `[mem_smul_iff]`.

Establish `e : x = (s : 𝒪[k]) • (g⁻¹ • x)` using `by rw [← hg, smul_inv_smul]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[e]`. Conclude with `L.smul_mem _ h`.

Introduce `h`. Establish `e' : g⁻¹ • x = ((s⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) • x` using `by conv_rhs => rw [e]`. Rewrite using `[smul_smul, Units.inv_mul, one_smul]`. Rewrite using `[e']`. Conclude with `L.smul_mem _ h`.

Establish `lift : ∀ c : 𝓀[k]ˣ, ∃ s : 𝒪[k]ˣ, (Units.map (residue 𝒪[k]).toMonoidHom s)⁻¹ = c`. Introduce `c`. Take `⟨t, ht⟩` from `IsLocalRing.residue_surjective ((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k])`. Establish `hu : IsUnit t`. Assume the negation of the conclusion as `hnu`.

Establish `h0 : residue 𝒪[k] t = 0` using `(IsLocalRing.residue_eq_zero_iff t).mpr ((IsLocalRing.mem_maximalIdeal t).mpr hnu)`. Rewrite `h0` using `[ht]`. Conclude with `(c⁻¹).ne_zero h0`. Use `⟨hu.unit, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_eq_iff_eq_inv]`.

Use `ext`. Simplify using `[ht]`. Establish `hθc : ∀ c : 𝓀[k]ˣ, θ (formOf π P v (c • P)) = θ v`. Introduce `c`. Take `⟨s, hs⟩` from `lift c`.

Take `⟨g, hg⟩` from `scal s`. Establish `hgP : g • P = c • P` using `by rw [scalar_smul_eq g s hg P, hs]`. Rewrite using `[← hgP, formOf_smul]`. Break down `hθ with h | h` into its components or cases. Conclude with `h g (stab g s hg P.lat) v`.

Conclude with `h g (stab g s hg P.ker) v`. Establish `hsum : ∑ c : 𝓀[k]ˣ, formOf π P v (c • P) = 0` using `(mem_Mram _).mp hv P`. Establish `h0` using `congrArg θ hsum`. Rewrite `h0` using `[map_sum, map_zero]`. Simplify using `only [hθc, Finset.sum_const, Finset.card_univ] at h0`.

Establish `hcard : (Fintype.card 𝓀[k]ˣ : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Rewrite `h0` using `[← Nat.cast_smul_eq_nsmul ℂ]`. Conclude with `(smul_eq_zero.mp h0).resolve_left hcard`.
-/
theorem vanishing [Fintype n] [DecidableEq n] (q : Unif k) : Vanishing k n M q where
  trLat_eq_zero φ h L _ := by
    rw [trLat_apply]
    exact Model.sum_stable_eq_zero h _ fun c P => by simp
  trKer_eq_zero φ h L _ := by
    rw [trKer_apply]
    exact Model.sum_stable_eq_zero h _ fun c P => by simp
  partial_lat φ h L _ S hS := by
    refine sum_family_eq_zero h (fun f => ofDual L f) (fun f g hfg => ?_) S fun c f hf => ?_
    · exact (latEquiv L).injective (Subtype.ext hfg)
    · exact ⟨⟨(c : 𝓀[k]) • f.1, smul_ne_zero c.ne_zero f.2⟩, hS c f _ hf rfl, (smul_ofDual L c f).symm⟩
  partial_ker φ h L _ S hS := by
    refine sum_family_eq_zero h (fun x => up L q x) (fun x y hxy => ?_) S fun c x hx => ?_
    · exact (kerEquiv L q).injective (Subtype.ext hxy)
    · exact ⟨⟨((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) • x.1, smul_ne_zero (c⁻¹).ne_zero x.2⟩, hS c⁻¹ x _ hx rfl,
        (smul_up L q c x).symm⟩
  invariant_eq_zero π P v hv M' _ _ θ hθ := by
    classical
    letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _

    have scal : ∀ s : 𝒪[k]ˣ, ∃ g : GL n k, ∀ x : n → k, g • x = (s : 𝒪[k]) • x := by
      intro s
      refine ⟨Units.map (Matrix.scalar n : k →+* Matrix n n k).toMonoidHom
        (Units.map (algebraMap 𝒪[k] k).toMonoidHom s), fun x => ?_⟩
      ext i
      simp [Units.smul_def, Matrix.scalar_apply, Matrix.mulVec_diagonal, Algebra.smul_def]

    have stab : ∀ (g : GL n k) (s : 𝒪[k]ˣ), (∀ x : n → k, g • x = (s : 𝒪[k]) • x) →
        ∀ L : Submodule 𝒪[k] (n → k), g ∈ latStab L := by
      intro g s hg L
      open Pointwise in rw [MulAction.mem_stabilizer_iff]
      ext x
      rw [mem_smul_iff]
      have e : x = (s : 𝒪[k]) • (g⁻¹ • x) := by rw [← hg, smul_inv_smul]
      constructor
      · intro h
        rw [e]
        exact L.smul_mem _ h
      · intro h
        have e' : g⁻¹ • x = ((s⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) • x := by
          conv_rhs => rw [e]
          rw [smul_smul, Units.inv_mul, one_smul]
        rw [e']
        exact L.smul_mem _ h

    have lift : ∀ c : 𝓀[k]ˣ, ∃ s : 𝒪[k]ˣ, (Units.map (residue 𝒪[k]).toMonoidHom s)⁻¹ = c := by
      intro c
      obtain ⟨t, ht⟩ := IsLocalRing.residue_surjective ((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k])
      have hu : IsUnit t := by
        by_contra hnu
        have h0 : residue 𝒪[k] t = 0 :=
          (IsLocalRing.residue_eq_zero_iff t).mpr ((IsLocalRing.mem_maximalIdeal t).mpr hnu)
        rw [ht] at h0
        exact (c⁻¹).ne_zero h0
      refine ⟨hu.unit, ?_⟩
      rw [inv_eq_iff_eq_inv]
      ext
      simp [ht]
    have hθc : ∀ c : 𝓀[k]ˣ, θ (formOf π P v (c • P)) = θ v := by
      intro c
      obtain ⟨s, hs⟩ := lift c
      obtain ⟨g, hg⟩ := scal s
      have hgP : g • P = c • P := by rw [scalar_smul_eq g s hg P, hs]
      rw [← hgP, formOf_smul]
      rcases hθ with h | h
      · exact h g (stab g s hg P.lat) v
      · exact h g (stab g s hg P.ker) v
    have hsum : ∑ c : 𝓀[k]ˣ, formOf π P v (c • P) = 0 := (mem_Mram _).mp hv P
    have h0 := congrArg θ hsum
    rw [map_sum, map_zero] at h0
    simp only [hθc, Finset.sum_const, Finset.card_univ] at h0
    have hcard : (Fintype.card 𝓀[k]ˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [← Nat.cast_smul_eq_nsmul ℂ] at h0
    exact (smul_eq_zero.mp h0).resolve_left hcard

/- English proof (translation)
Rewrite using `[cross_dia_left q (by rw [Pair.dia_lat]; exact h), cross_dia_right q h]`. Simplify using the standard rewrite rules.
-/
theorem cross_dia (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) (c : 𝓀[k]ˣ) :
    cross q (c • P₁) (c • P) = cross q P₁ P := by
  rw [cross_dia_left q (by rw [Pair.dia_lat]; exact h), cross_dia_right q h]
  simp

/- English proof (translation)
Use `LinearMap.ext fun φ => funext fun P => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, sumOp_apply, dia_apply]`. Use `Finset.sum_nbij' (fun Q => c • Q) (fun Q => c⁻¹ • Q) (fun Q hQ => (hS P Q).mp hQ) (fun Q hQ => (hS P (c⁻¹ • Q)).mpr (by rwa [smul_inv_smul])) (fun Q _ => inv_smul_smul c Q) (fun Q _ => smul_inv_smul c Q) fun Q hQ => ?_` and prove the remaining obligations. Rewrite using `[hw P Q hQ]`.
-/
theorem sumOp_dia (S : Pair k n → Finset (Pair k n)) (w : Pair k n → Pair k n → ℂ) (c : 𝓀[k]ˣ)
    (hS : ∀ P Q, Q ∈ S P ↔ c • Q ∈ S (c • P)) (hw : ∀ P, ∀ Q ∈ S P, w (c • P) (c • Q) = w P Q) :
    (sumOp S w * dia c : Module.End ℂ (Form k n M)) = dia c * sumOp S w := by
  refine LinearMap.ext fun φ => funext fun P => ?_
  simp only [Module.End.mul_apply, sumOp_apply, dia_apply]
  refine Finset.sum_nbij' (fun Q => c • Q) (fun Q => c⁻¹ • Q) (fun Q hQ => (hS P Q).mp hQ)
    (fun Q hQ => (hS P (c⁻¹ • Q)).mpr (by rwa [smul_inv_smul])) (fun Q _ => inv_smul_smul c Q)
    (fun Q _ => smul_inv_smul c Q) fun Q hQ => ?_
  rw [hw P Q hQ]

variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)

/- English proof (translation)
Unfold `D Da`. Use `sumOp_dia _ _ c (fun P Q => ?_) fun _ _ _ => rfl` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, mem_withLat, Pair.dia_lat, Pair.dia_ker]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, h'⟩; exact ⟨h, by rw [cross_dia q h, h']⟩`.

Introduce and unpack `⟨h, h'⟩; exact ⟨h, by rw [← cross_dia q h c, h']⟩`.
-/
theorem D_dia (c : 𝓀[k]ˣ) : (D q * dia c : Module.End ℂ (Form k n M)) = dia c * D q := by
  unfold D Da
  refine sumOp_dia _ _ c (fun P Q => ?_) fun _ _ _ => rfl
  simp only [Finset.mem_filter, mem_withLat, Pair.dia_lat, Pair.dia_ker]
  constructor
  · rintro ⟨h, h'⟩; exact ⟨h, by rw [cross_dia q h, h']⟩
  · rintro ⟨h, h'⟩; exact ⟨h, by rw [← cross_dia q h c, h']⟩

/- English proof (translation)
Unfold `U`. Use `sumOp_dia _ _ c (fun P Q => ?_) fun _ _ _ => rfl` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, mem_withKer, Pair.dia_lat, Pair.dia_ker]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, h'⟩; exact ⟨h, by rw [cross_dia q h.symm, h']⟩`.

Introduce and unpack `⟨h, h'⟩; exact ⟨h, by rw [← cross_dia q h.symm c, h']⟩`.
-/
theorem U_dia (c : 𝓀[k]ˣ) : (U q * dia c : Module.End ℂ (Form k n M)) = dia c * U q := by
  unfold U
  refine sumOp_dia _ _ c (fun P Q => ?_) fun _ _ _ => rfl
  simp only [Finset.mem_filter, mem_withKer, Pair.dia_lat, Pair.dia_ker]
  constructor
  · rintro ⟨h, h'⟩; exact ⟨h, by rw [cross_dia q h.symm, h']⟩
  · rintro ⟨h, h'⟩; exact ⟨h, by rw [← cross_dia q h.symm c, h']⟩

/- English proof (translation)
Unfold `FF`. Use `sumOp_dia _ _ c (fun P Q => by simp) fun P Q hQ => ?_` and prove the remaining obligations. Rewrite using `[cross_dia q (mem_withLat.mp hQ)]`.
-/
theorem FF_dia (c : 𝓀[k]ˣ) : (FF q χ * dia c : Module.End ℂ (Form k n M)) = dia c * FF q χ := by
  unfold FF
  refine sumOp_dia _ _ c (fun P Q => by simp) fun P Q hQ => ?_
  rw [cross_dia q (mem_withLat.mp hQ)]

/- English proof (translation)
Unfold `FFStar`. Use `sumOp_dia _ _ c (fun P Q => by simp) fun P Q hQ => ?_` and prove the remaining obligations. Rewrite using `[cross_dia q (mem_withKer.mp hQ).symm]`.
-/
theorem FFStar_dia (c : 𝓀[k]ˣ) : (FFStar q χ * dia c : Module.End ℂ (Form k n M)) = dia c * FFStar q χ := by
  unfold FFStar
  refine sumOp_dia _ _ c (fun P Q => by simp) fun P Q hQ => ?_
  rw [cross_dia q (mem_withKer.mp hQ).symm]

/- English proof (translation)
Rewrite using `[← map_mul, ← map_mul, mul_comm]`.
-/
theorem dia_dia (d c : 𝓀[k]ˣ) : (dia d * dia c : Module.End ℂ (Form k n M)) = dia c * dia d := by
  rw [← map_mul, ← map_mul, mul_comm]

/- English proof (translation)
Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, smul_mul_assoc, h]`.
-/
theorem commute_sum {A : Module.End ℂ (Form k n M)} (h : ∀ c : 𝓀[k]ˣ, A * dia c = dia c * A) {ι : Type}
    (s : Finset ι) (a : ι → ℂ) (e : ι → 𝓀[k]ˣ) :
    A * (∑ i ∈ s, a i • dia (e i)) = (∑ i ∈ s, a i • dia (e i)) * A := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, h]

/- English proof (translation)
Simplify using `only [Mram, LinearMap.mem_ker] at hφ ⊢`. Establish `hc : (Nm : Module.End ℂ (Form k n M)) * A = A * Nm`. Unfold `Nm`. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun c _ => (h c).symm`.

Rewrite using `[← Module.End.mul_apply, hc, Module.End.mul_apply, hφ, map_zero]`.
-/
theorem mem_ram {A : Module.End ℂ (Form k n M)} (h : ∀ c : 𝓀[k]ˣ, A * dia c = dia c * A) {φ : Form k n M}
    (hφ : φ ∈ Mram k n M) : A φ ∈ Mram k n M := by
  simp only [Mram, LinearMap.mem_ker] at hφ ⊢
  have hc : (Nm : Module.End ℂ (Form k n M)) * A = A * Nm := by
    unfold Nm
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => (h c).symm
  rw [← Module.End.mul_apply, hc, Module.End.mul_apply, hφ, map_zero]

/- English proof (translation)
Unfold `GsStar`. Conclude with `(commute_sum (fun d => dia_dia c d) _ (fun d : 𝓀[k]ˣ => χ (-(d : 𝓀[k]))) fun d => d⁻¹).symm`.
-/
theorem GsStar_dia (c : 𝓀[k]ˣ) : (GsStar χ * dia c : Module.End ℂ (Form k n M)) = dia c * GsStar χ := by
  unfold GsStar
  exact (commute_sum (fun d => dia_dia c d) _ (fun d : 𝓀[k]ˣ => χ (-(d : 𝓀[k]))) fun d => d⁻¹).symm

variable {χ}

/- English proof (translation)
Use `letI : Fintype 𝓀[k] := Fintype.ofFinite _`. Establish `hsplit : ∀ f : 𝓀[k] → ℂ, ∑ d : 𝓀[k]ˣ, f d = ∑ x : 𝓀[k], f x - f 0`. Introduce `f`. Rewrite using `[← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : 𝓀[k])), add_sub_cancel_right]`. Conclude with `Finset.sum_bij' (fun d _ => (d : 𝓀[k])) (fun x hx => Units.mk0 x (Finset.ne_of_mem_erase hx)) (fun d _ => Finset.mem_erase.mpr ⟨d.ne_zero, Finset.mem_univ _⟩) (fun x _ => Finset.mem_univ _) (fun d _ => Units.ext rfl) (fun x _ => rfl) (fun d _ => rfl)`.

Rewrite using `[hsplit (fun x => χ (x * a)), zero_mul, AddChar.map_zero_eq_one]`. Use `split_ifs with ha`. Substitute `ha` using the available equality. Simplify using `[resCard, Nat.card_eq_fintype_card]`. Establish `hz : ∑ x : 𝓀[k], χ (x * a) = 0`.

Rewrite using `[← AddChar.sum_eq_zero_of_ne_one hχ]`. Conclude with `Fintype.sum_bijective (· * a) (mulRight_bijective₀ a ha) _ _ fun x => rfl`. Rewrite using `[hz, zero_sub]`.
-/
theorem sum_units_char [Fintype 𝓀[k]ˣ] (hχ : χ ≠ 1) (a : 𝓀[k]) [Decidable (a = 0)] :
    ∑ d : 𝓀[k]ˣ, χ (d * a) = (if a = 0 then (resCard k : ℂ) else 0) - 1 := by
  classical
  letI : Fintype 𝓀[k] := Fintype.ofFinite _
  have hsplit : ∀ f : 𝓀[k] → ℂ, ∑ d : 𝓀[k]ˣ, f d = ∑ x : 𝓀[k], f x - f 0 := by
    intro f
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : 𝓀[k])), add_sub_cancel_right]
    exact Finset.sum_bij' (fun d _ => (d : 𝓀[k])) (fun x hx => Units.mk0 x (Finset.ne_of_mem_erase hx))
      (fun d _ => Finset.mem_erase.mpr ⟨d.ne_zero, Finset.mem_univ _⟩) (fun x _ => Finset.mem_univ _)
      (fun d _ => Units.ext rfl) (fun x _ => rfl) (fun d _ => rfl)
  rw [hsplit (fun x => χ (x * a)), zero_mul, AddChar.map_zero_eq_one]
  split_ifs with ha
  · subst ha
    simp [resCard, Nat.card_eq_fintype_card]
  · have hz : ∑ x : 𝓀[k], χ (x * a) = 0 := by
      rw [← AddChar.sum_eq_zero_of_ne_one hχ]
      exact Fintype.sum_bijective (· * a) (mulRight_bijective₀ a ha) _ _ fun x => rfl
    rw [hz, zero_sub]

/- English proof (translation)
Use `letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _`. Use `LinearMap.ext fun φ => funext fun P => ?_` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply, Gs_apply, LinearMap.sub_apply, Pi.sub_apply, Nm_apply, LinearMap.smul_apply, Pi.smul_apply, Module.End.one_apply]`. Simplify using `only [GsStar_apply, Finset.smul_sum, smul_smul]`. Establish `hre : ∀ c : 𝓀[k]ˣ, ∑ d : 𝓀[k]ˣ, (χ c * χ (-(d : 𝓀[k]))) • φ ((d⁻¹ * c) • P) = ∑ u : 𝓀[k]ˣ, χ (c * (1 - ((u⁻¹ : 𝓀[k]ˣ) : 𝓀[k]))) • φ (u • P)`.

Introduce `c`. Use `Fintype.sum_equiv ⟨fun d => d⁻¹ * c, fun u => c * u⁻¹, fun d => by simp, fun u => by simp⟩ _ _ fun d => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_fn_mk, ← AddChar.map_add_eq_mul]`. Use `congr 2`. Simplify using `[_root_.mul_inv_rev, sub_eq_add_neg]`.

Rewrite using `[mul_add, mul_one, mul_neg, ← mul_assoc, mul_inv_cancel₀ c.ne_zero, one_mul]`. Simplify using `only [hre]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul, sum_units_char hχ, sub_smul, Finset.sum_sub_distrib, one_smul, sub_eq_zero, ite_smul, zero_smul]`. Rewrite using `[Finset.sum_eq_single (1 : 𝓀[k]ˣ)]`.

Simplify using the standard rewrite rules. Introduce `u _ hu`. Rewrite using `[if_neg]`. Introduce `h0`. Apply `hu` to reduce the goal to its premises.

Use `ext`. Establish `: ((u⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) = 1`. Conclude with `h0.symm`. Simplify using `using this`. Simplify using the standard rewrite rules.
-/
theorem Gs_mul_GsStar (hχ : χ ≠ 1) :
    (Gs χ * GsStar χ : Module.End ℂ (Form k n M)) = (resCard k : ℂ) • 1 - Nm := by
  classical
  letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _
  refine LinearMap.ext fun φ => funext fun P => ?_
  rw [Module.End.mul_apply, Gs_apply, LinearMap.sub_apply, Pi.sub_apply, Nm_apply, LinearMap.smul_apply,
    Pi.smul_apply, Module.End.one_apply]
  simp only [GsStar_apply, Finset.smul_sum, smul_smul]
  have hre : ∀ c : 𝓀[k]ˣ, ∑ d : 𝓀[k]ˣ, (χ c * χ (-(d : 𝓀[k]))) • φ ((d⁻¹ * c) • P) =
      ∑ u : 𝓀[k]ˣ, χ (c * (1 - ((u⁻¹ : 𝓀[k]ˣ) : 𝓀[k]))) • φ (u • P) := by
    intro c
    refine Fintype.sum_equiv ⟨fun d => d⁻¹ * c, fun u => c * u⁻¹, fun d => by simp, fun u => by simp⟩ _ _
      fun d => ?_
    simp only [Equiv.coe_fn_mk, ← AddChar.map_add_eq_mul]
    congr 2
    simp [_root_.mul_inv_rev, sub_eq_add_neg]
    rw [mul_add, mul_one, mul_neg, ← mul_assoc, mul_inv_cancel₀ c.ne_zero, one_mul]
  simp only [hre]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, sum_units_char hχ, sub_smul, Finset.sum_sub_distrib, one_smul, sub_eq_zero,
    ite_smul, zero_smul]
  rw [Finset.sum_eq_single (1 : 𝓀[k]ˣ)]
  · simp
  · intro u _ hu
    rw [if_neg]
    intro h0
    apply hu
    ext
    have : ((u⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) = 1 := by
      exact h0.symm
    simpa using this
  · simp

/- English proof (translation)
Establish `hc : (GsStar χ * Gs χ : Module.End ℂ (Form k n M)) = Gs χ * GsStar χ`. Unfold `Gs`. Conclude with `commute_sum (fun c => GsStar_dia χ c) _ (fun d : 𝓀[k]ˣ => χ d) fun d => d`. Rewrite using `[hc, Gs_mul_GsStar hχ]`.
-/
theorem GsStar_mul_Gs (hχ : χ ≠ 1) :
    (GsStar χ * Gs χ : Module.End ℂ (Form k n M)) = (resCard k : ℂ) • 1 - Nm := by
  have hc : (GsStar χ * Gs χ : Module.End ℂ (Form k n M)) = Gs χ * GsStar χ := by
    unfold Gs
    exact commute_sum (fun c => GsStar_dia χ c) _ (fun d : 𝓀[k]ˣ => χ d) fun d => d
  rw [hc, Gs_mul_GsStar hχ]

/- English proof (translation)
Rewrite using `[eq_sub_iff_add_eq, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : V))]`. Use `congr 1`. Conclude with `Finset.sum_bij' (fun v _ => v.1) (fun v hv => ⟨v, Finset.ne_of_mem_erase hv⟩) (fun v _ => Finset.mem_erase.mpr ⟨v.2, Finset.mem_univ _⟩) (fun v _ => Finset.mem_univ _) (fun v _ => rfl) (fun v _ => rfl) (fun v _ => rfl)`.
-/
private theorem sum_subtype_ne_zero_eq_sum_sub_zero {V : Type} [Zero V] [Fintype V] [DecidableEq V] [Fintype {v : V // v ≠ 0}]
    (g : V → ℂ) : ∑ v : {v : V // v ≠ 0}, g v.1 = ∑ v, g v - g 0 := by
  rw [eq_sub_iff_add_eq, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : V))]
  congr 1
  exact Finset.sum_bij' (fun v _ => v.1) (fun v hv => ⟨v, Finset.ne_of_mem_erase hv⟩)
    (fun v _ => Finset.mem_erase.mpr ⟨v.2, Finset.mem_univ _⟩) (fun v _ => Finset.mem_univ _)
    (fun v _ => rfl) (fun v _ => rfl) (fun v _ => rfl)

/- English proof (translation)
Use function extensionality and compare the values at `P₁`. Rewrite using `[FF_apply, Pi.sub_apply, Pi.smul_apply, tr'_apply]`. Use `set L := P₁.ker with hL`. Use `haveI : L.IsLattice k := by rw [hL]; infer_instance`. Use `letI : Fintype {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0} := Fintype.ofFinite _`.

Use `letI : Fintype {x : Red L // x ≠ 0} := Fintype.ofFinite _`. Use `letI : Fintype (Module.Dual 𝓀[k] (Red L)) := Fintype.ofFinite _`. Use `letI : Fintype (Red L) := Fintype.ofFinite _`. Use `letI : Fintype 𝓀[k] := Fintype.ofFinite _`. Take `⟨x₁, hx₁⟩ : ∃ x₁ : {x : Red L // x ≠ 0}, up L q x₁ = P₁` from `⟨_, congrArg Subtype.val ((kerEquiv L q).apply_symm_apply ⟨P₁, hL.symm⟩)⟩`.

Rewrite using `[← hx₁, sum_withLat L, sum_withKer L q]`. Simplify using `only [FFStar_ofDual, cross_up_ofDual, Finset.smul_sum, smul_smul, ← AddChar.map_add_eq_mul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul]`. Establish `hinner : ∀ x : {x : Red L // x ≠ 0}, ∑ f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}, χ (f.1 x₁.1 + -f.1 x.1) = (if x = x₁ then (resCard k : ℂ) ^ Fintype.card n else 0) - 1`.

Introduce `x`. Rewrite using `[sum_subtype_ne_zero_eq_sum_sub_zero (fun f : Module.Dual 𝓀[k] (Red L) => χ (f x₁.1 + -f x.1))]`. Simplify using `only [LinearMap.zero_apply, neg_zero, add_zero, AddChar.map_zero_eq_one]`. Use `congr 1`. Establish `e : ∀ f : Module.Dual 𝓀[k] (Red L), f x₁.1 + -f x.1 = Module.Dual.eval 𝓀[k] (Red L) (x₁.1 - x.1) f`.

Introduce `f`. Simplify using `[sub_eq_add_neg]`. Simplify using `only [e]`. Rewrite using `[Model.sum_char hχ]`. Establish `hiff : Module.Dual.eval 𝓀[k] (Red L) (x₁.1 - x.1) = 0 ↔ x = x₁`.

Prove the components needed by the constructor for the conclusion. Introduce `h0`. Establish `h1 : x₁.1 - x.1 = 0` using `(Module.forall_dual_apply_eq_zero_iff 𝓀[k] _).mp fun f => by`. Simplify using `using LinearMap.congr_fun h0 f`. Conclude with `(Subtype.ext (sub_eq_zero.mp h1)).symm`.

Introduce and unpack `rfl`. Simplify using the standard rewrite rules. Establish `hcard : (Fintype.card (Module.Dual 𝓀[k] (Red L)) : ℂ) = (resCard k : ℂ) ^ Fintype.card n`. Rewrite using `[Module.card_eq_pow_finrank (K := 𝓀[k]), Subspace.dual_finrank_eq, Red.finrank_eq]`. Simplify using `[resCard, Nat.card_eq_fintype_card]`.

Simplify using `only [hiff, hcard]`. Simplify using `only [hinner, sub_smul, ite_smul, zero_smul, one_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem FF_FFStar [Fintype n] (hχ : χ ≠ 1) (φ : Form k n M) :
    FF q χ (FFStar q χ φ) = (resCard k ^ Fintype.card n : ℂ) • φ - tr' φ := by
  classical
  funext P₁
  rw [FF_apply, Pi.sub_apply, Pi.smul_apply, tr'_apply]
  set L := P₁.ker with hL
  haveI : L.IsLattice k := by rw [hL]; infer_instance
  letI : Fintype {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0} := Fintype.ofFinite _
  letI : Fintype {x : Red L // x ≠ 0} := Fintype.ofFinite _
  letI : Fintype (Module.Dual 𝓀[k] (Red L)) := Fintype.ofFinite _
  letI : Fintype (Red L) := Fintype.ofFinite _
  letI : Fintype 𝓀[k] := Fintype.ofFinite _
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : {x : Red L // x ≠ 0}, up L q x₁ = P₁ :=
    ⟨_, congrArg Subtype.val ((kerEquiv L q).apply_symm_apply ⟨P₁, hL.symm⟩)⟩
  rw [← hx₁, sum_withLat L, sum_withKer L q]
  simp only [FFStar_ofDual, cross_up_ofDual, Finset.smul_sum, smul_smul, ← AddChar.map_add_eq_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have hinner : ∀ x : {x : Red L // x ≠ 0}, ∑ f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0},
      χ (f.1 x₁.1 + -f.1 x.1) = (if x = x₁ then (resCard k : ℂ) ^ Fintype.card n else 0) - 1 := by
    intro x
    rw [sum_subtype_ne_zero_eq_sum_sub_zero (fun f : Module.Dual 𝓀[k] (Red L) => χ (f x₁.1 + -f x.1))]
    simp only [LinearMap.zero_apply, neg_zero, add_zero, AddChar.map_zero_eq_one]
    congr 1
    have e : ∀ f : Module.Dual 𝓀[k] (Red L),
        f x₁.1 + -f x.1 = Module.Dual.eval 𝓀[k] (Red L) (x₁.1 - x.1) f := by
      intro f
      simp [sub_eq_add_neg]
    simp only [e]
    rw [Model.sum_char hχ]
    have hiff : Module.Dual.eval 𝓀[k] (Red L) (x₁.1 - x.1) = 0 ↔ x = x₁ := by
      constructor
      · intro h0
        have h1 : x₁.1 - x.1 = 0 := (Module.forall_dual_apply_eq_zero_iff 𝓀[k] _).mp fun f => by
          simpa using LinearMap.congr_fun h0 f
        exact (Subtype.ext (sub_eq_zero.mp h1)).symm
      · rintro rfl
        simp
    have hcard : (Fintype.card (Module.Dual 𝓀[k] (Red L)) : ℂ) = (resCard k : ℂ) ^ Fintype.card n := by
      rw [Module.card_eq_pow_finrank (K := 𝓀[k]), Subspace.dual_finrank_eq, Red.finrank_eq]
      simp [resCard, Nat.card_eq_fintype_card]
    simp only [hiff, hcard]
  simp only [hinner, sub_smul, ite_smul, zero_smul, one_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

variable (χ) in

/- English proof (translation)
Use `letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _`. Use function extensionality and compare the values at `P`. Rewrite using `[FFStar_apply, U_apply]`. Simplify using `only [GsStar_apply]`. Establish `h0 : ∑ P₁ ∈ withKer P.lat with cross q P₁ P = 0, χ (-cross q P₁ P) • φ P₁ = 0`.

Rewrite using `[Finset.sum_congr rfl fun P₁ hP₁ => by`. Rewrite using `[(Finset.mem_filter.mp hP₁).2, neg_zero, AddChar.map_zero_eq_one, one_smul]]`. Use `Model.sum_stable_eq_zero h _ fun c P₁ => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, mem_withKer, Pair.dia_ker]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hk, hc⟩`. Use `⟨hk, ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[cross_dia_left q hk.symm, mul_eq_zero, or_iff_right (Units.ne_zero _)]`. Then use the resulting hypothesis. Introduce and unpack `⟨hk, hc⟩`. Conclude with `⟨hk, by rw [cross_dia_left q hk.symm, hc, mul_zero]⟩`.

Rewrite using `[← Finset.sum_filter_add_sum_filter_not (withKer P.lat) (fun P₁ => cross q P₁ P = 0), h0, zero_add, ← Finset.sum_product']`. Use `Finset.sum_bij' (fun P₁ hP₁ => (Units.mk0 (cross q P₁ P) (Finset.mem_filter.mp hP₁).2 • P₁, Units.mk0 (cross q P₁ P) (Finset.mem_filter.mp hP₁).2)) (fun x _ => x.2⁻¹ • x.1) (fun P₁ hP₁ => ?_) (fun x hx => ?_) (fun P₁ _ => inv_smul_smul _ _) (fun x hx => ?_) (fun P₁ _ => by simp)` and prove the remaining obligations. Take `⟨hk, hc⟩` from `Finset.mem_filter.mp hP₁`. Use `Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩` and prove the remaining obligations. Rewrite using `[mem_withKer, Pair.dia_ker]`.

Conclude with `mem_withKer.mp hk`. Rewrite using `[cross_dia_left q (mem_withKer.mp hk).symm]`. Simplify using `[hc]`. Take `⟨h1, -⟩` from `Finset.mem_product.mp hx`. Take `⟨hk, hc⟩` from `Finset.mem_filter.mp h1`.

Use `Finset.mem_filter.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_withKer, Pair.dia_ker]`. Conclude with `mem_withKer.mp hk`. Rewrite using `[cross_dia_left q (mem_withKer.mp hk).symm, hc, inv_inv, mul_one]`. Conclude with `x.2.ne_zero`.

Take `⟨h1, -⟩` from `Finset.mem_product.mp hx`. Take `⟨hk, hc⟩` from `Finset.mem_filter.mp h1`. Establish `e : cross q (x.2⁻¹ • x.1) P = x.2`. Rewrite using `[cross_dia_left q (mem_withKer.mp hk).symm, hc, inv_inv, mul_one]`. Establish `eu : ∀ h', Units.mk0 (cross q (x.2⁻¹ • x.1) P) h' = x.2` using `fun h' => Units.ext (by simpa using e)`.

Rewrite using `[eu]`. Conclude with `Prod.ext (smul_inv_smul _ _) rfl`.
-/
theorem FFStar_eq_U_GsStar {φ : Form k n M} (h : φ ∈ Mram k n M) : FFStar q χ φ = U q (GsStar χ φ) := by
  classical
  letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _
  funext P
  rw [FFStar_apply, U_apply]
  simp only [GsStar_apply]

  have h0 : ∑ P₁ ∈ withKer P.lat with cross q P₁ P = 0, χ (-cross q P₁ P) • φ P₁ = 0 := by
    rw [Finset.sum_congr rfl fun P₁ hP₁ => by
      rw [(Finset.mem_filter.mp hP₁).2, neg_zero, AddChar.map_zero_eq_one, one_smul]]
    refine Model.sum_stable_eq_zero h _ fun c P₁ => ?_
    simp only [Finset.mem_filter, mem_withKer, Pair.dia_ker]
    constructor
    · rintro ⟨hk, hc⟩
      refine ⟨hk, ?_⟩
      rwa [cross_dia_left q hk.symm, mul_eq_zero, or_iff_right (Units.ne_zero _)] at hc
    · rintro ⟨hk, hc⟩
      exact ⟨hk, by rw [cross_dia_left q hk.symm, hc, mul_zero]⟩
  rw [← Finset.sum_filter_add_sum_filter_not (withKer P.lat) (fun P₁ => cross q P₁ P = 0), h0, zero_add,
    ← Finset.sum_product']
  refine Finset.sum_bij'
    (fun P₁ hP₁ => (Units.mk0 (cross q P₁ P) (Finset.mem_filter.mp hP₁).2 • P₁,
      Units.mk0 (cross q P₁ P) (Finset.mem_filter.mp hP₁).2))
    (fun x _ => x.2⁻¹ • x.1) (fun P₁ hP₁ => ?_) (fun x hx => ?_) (fun P₁ _ => inv_smul_smul _ _)
    (fun x hx => ?_) (fun P₁ _ => by simp)
  · obtain ⟨hk, hc⟩ := Finset.mem_filter.mp hP₁
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · rw [mem_withKer, Pair.dia_ker]
      exact mem_withKer.mp hk
    · rw [cross_dia_left q (mem_withKer.mp hk).symm]
      simp [hc]
  · obtain ⟨h1, -⟩ := Finset.mem_product.mp hx
    obtain ⟨hk, hc⟩ := Finset.mem_filter.mp h1
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [mem_withKer, Pair.dia_ker]
      exact mem_withKer.mp hk
    · rw [cross_dia_left q (mem_withKer.mp hk).symm, hc, inv_inv, mul_one]
      exact x.2.ne_zero
  · obtain ⟨h1, -⟩ := Finset.mem_product.mp hx
    obtain ⟨hk, hc⟩ := Finset.mem_filter.mp h1
    have e : cross q (x.2⁻¹ • x.1) P = x.2 := by
      rw [cross_dia_left q (mem_withKer.mp hk).symm, hc, inv_inv, mul_one]
    have eu : ∀ h', Units.mk0 (cross q (x.2⁻¹ • x.1) P) h' = x.2 := fun h' => Units.ext (by simpa using e)
    rw [eu]
    exact Prod.ext (smul_inv_smul _ _) rfl

/- English proof (translation)
Unfold `resCard`. Conclude with `(Nat.card_pos (α := 𝓀[k])).ne'` after adjusting the coercions.
-/
theorem resCard_ne_zero : (resCard k : ℂ) ≠ 0 := by
  unfold resCard
  exact_mod_cast (Nat.card_pos (α := 𝓀[k])).ne'

/- English proof (translation)
Rewrite using `[Model.FFStar_FF q hχ φ, (Model.tr_eq_zero h).1, sub_zero]`.
-/
theorem FFStar_FF_ram [Fintype n] (hχ : χ ≠ 1) {φ : Form k n M} (h : φ ∈ Mram k n M) :
    FFStar q χ (FF q χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ := by
  rw [Model.FFStar_FF q hχ φ, (Model.tr_eq_zero h).1, sub_zero]

/- English proof (translation)
Rewrite using `[FF_FFStar q hχ φ, (Model.tr_eq_zero h).2, sub_zero]`.
-/
theorem FF_FFStar_ram [Fintype n] (hχ : χ ≠ 1) {φ : Form k n M} (h : φ ∈ Mram k n M) :
    FF q χ (FFStar q χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ := by
  rw [FF_FFStar q hχ φ, (Model.tr_eq_zero h).2, sub_zero]

/- English proof (translation)
Establish `hq` using `resCard_ne_zero (k := k)`. Establish `e : φ' = ((resCard k : ℂ)⁻¹ * (resCard k : ℂ) ^ r) • φ`. Rewrite using `[mul_smul, ← h, smul_smul, inv_mul_cancel₀ hq, one_smul]`. Rewrite using `[e, zpow_sub₀ hq, zpow_natCast, zpow_one, div_eq_inv_mul]`.
-/
theorem eq_zpow_smul {φ φ' : Form k n M} {r : ℕ} (h : (resCard k : ℂ) • φ' = ((resCard k : ℂ) ^ r) • φ) :
    φ' = ((resCard k : ℂ) ^ ((r : ℤ) - 1)) • φ := by
  have hq := resCard_ne_zero (k := k)
  have e : φ' = ((resCard k : ℂ)⁻¹ * (resCard k : ℂ) ^ r) • φ := by
    rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hq, one_smul]
  rw [e, zpow_sub₀ hq, zpow_natCast, zpow_one, div_eq_inv_mul]

/- English proof (translation)
Use `letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _`. Use function extensionality and compare the values at `P₁`. Rewrite using `[FF_apply, D_apply]`. Simplify using `only [Gs_apply]`. Establish `h0 : ∑ P ∈ withLat P₁.ker with cross q P₁ P = 0, χ (cross q P₁ P) • φ P = 0`.

Rewrite using `[Finset.sum_congr rfl fun P hP => by`. Rewrite using `[(Finset.mem_filter.mp hP).2, AddChar.map_zero_eq_one, one_smul]]`. Use `Model.sum_stable_eq_zero h _ fun c P => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, mem_withLat, Pair.dia_lat]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hk, hc⟩`. Use `⟨hk, ?_⟩` and prove the remaining obligations. Rewrite `hc` using `[cross_dia_right q hk, mul_eq_zero, or_iff_right (Units.ne_zero _)]`. Then use the resulting hypothesis. Introduce and unpack `⟨hk, hc⟩`. Conclude with `⟨hk, by rw [cross_dia_right q hk, hc, mul_zero]⟩`.

Rewrite using `[← Finset.sum_filter_add_sum_filter_not (withLat P₁.ker) (fun P => cross q P₁ P = 0), h0, zero_add, ← Finset.sum_product']`. Use `Finset.sum_bij' (fun P hP => ((Units.mk0 (cross q P₁ P) (Finset.mem_filter.mp hP).2)⁻¹ • P, Units.mk0 (cross q P₁ P) (Finset.mem_filter.mp hP).2)) (fun x _ => x.2 • x.1) (fun P hP => ?_) (fun x hx => ?_) (fun P _ => smul_inv_smul _ _) (fun x hx => ?_) (fun P _ => by simp)` and prove the remaining obligations. Take `⟨hk, hc⟩` from `Finset.mem_filter.mp hP`. Use `Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩` and prove the remaining obligations. Rewrite using `[mem_withLat, Pair.dia_lat]`.

Conclude with `mem_withLat.mp hk`. Rewrite using `[cross_dia_right q (mem_withLat.mp hk)]`. Simplify using `[hc]`. Take `⟨h1, -⟩` from `Finset.mem_product.mp hx`. Take `⟨hk, hc⟩` from `Finset.mem_filter.mp h1`.

Use `Finset.mem_filter.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_withLat, Pair.dia_lat]`. Conclude with `mem_withLat.mp hk`. Rewrite using `[cross_dia_right q (mem_withLat.mp hk), hc, mul_one]`. Conclude with `x.2.ne_zero`.

Take `⟨h1, -⟩` from `Finset.mem_product.mp hx`. Take `⟨hk, hc⟩` from `Finset.mem_filter.mp h1`. Establish `e : cross q P₁ (x.2 • x.1) = x.2`. Rewrite using `[cross_dia_right q (mem_withLat.mp hk), hc, mul_one]`. Establish `eu : ∀ h', Units.mk0 (cross q P₁ (x.2 • x.1)) h' = x.2` using `fun h' => Units.ext (by simpa using e)`.

Rewrite using `[eu]`. Conclude with `Prod.ext (inv_smul_smul _ _) rfl`.
-/
private theorem FF_eq_D_Gs_of_mem_Mram {φ : Form k n M} (h : φ ∈ Mram k n M) : FF q χ φ = D q (Gs χ φ) := by
  classical
  letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _
  funext P₁
  rw [FF_apply, D_apply]
  simp only [Gs_apply]
  have h0 : ∑ P ∈ withLat P₁.ker with cross q P₁ P = 0, χ (cross q P₁ P) • φ P = 0 := by
    rw [Finset.sum_congr rfl fun P hP => by
      rw [(Finset.mem_filter.mp hP).2, AddChar.map_zero_eq_one, one_smul]]
    refine Model.sum_stable_eq_zero h _ fun c P => ?_
    simp only [Finset.mem_filter, mem_withLat, Pair.dia_lat]
    constructor
    · rintro ⟨hk, hc⟩
      refine ⟨hk, ?_⟩
      rwa [cross_dia_right q hk, mul_eq_zero, or_iff_right (Units.ne_zero _)] at hc
    · rintro ⟨hk, hc⟩
      exact ⟨hk, by rw [cross_dia_right q hk, hc, mul_zero]⟩
  rw [← Finset.sum_filter_add_sum_filter_not (withLat P₁.ker) (fun P => cross q P₁ P = 0), h0, zero_add,
    ← Finset.sum_product']
  refine Finset.sum_bij'
    (fun P hP => ((Units.mk0 (cross q P₁ P) (Finset.mem_filter.mp hP).2)⁻¹ • P,
      Units.mk0 (cross q P₁ P) (Finset.mem_filter.mp hP).2))
    (fun x _ => x.2 • x.1) (fun P hP => ?_) (fun x hx => ?_) (fun P _ => smul_inv_smul _ _)
    (fun x hx => ?_) (fun P _ => by simp)
  · obtain ⟨hk, hc⟩ := Finset.mem_filter.mp hP
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · rw [mem_withLat, Pair.dia_lat]
      exact mem_withLat.mp hk
    · rw [cross_dia_right q (mem_withLat.mp hk)]
      simp [hc]
  · obtain ⟨h1, -⟩ := Finset.mem_product.mp hx
    obtain ⟨hk, hc⟩ := Finset.mem_filter.mp h1
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [mem_withLat, Pair.dia_lat]
      exact mem_withLat.mp hk
    · rw [cross_dia_right q (mem_withLat.mp hk), hc, mul_one]
      exact x.2.ne_zero
  · obtain ⟨h1, -⟩ := Finset.mem_product.mp hx
    obtain ⟨hk, hc⟩ := Finset.mem_filter.mp h1
    have e : cross q P₁ (x.2 • x.1) = x.2 := by
      rw [cross_dia_right q (mem_withLat.mp hk), hc, mul_one]
    have eu : ∀ h', Units.mk0 (cross q P₁ (x.2 • x.1)) h' = x.2 := fun h' => Units.ext (by simpa using e)
    rw [eu]
    exact Prod.ext (inv_smul_smul _ _) rfl

/- English proof (translation)
Establish `hGsU : ∀ ψ : Form k n M, Gs χ (U q ψ) = U q (Gs χ ψ)` using `fun ψ => by`. Establish `e : (Gs χ * U q : Module.End ℂ (Form k n M)) = U q * Gs χ`. Unfold `Gs`. Conclude with `(commute_sum (fun c => U_dia q c) _ (fun d : 𝓀[k]ˣ => χ d) fun d => d).symm`. Conclude with `LinearMap.congr_fun e ψ`.

Establish `hN : Nm φ = 0` using `h`. Establish `h2 : FFStar q χ φ ∈ Mram k n M` using `mem_ram (fun c => FFStar_dia q χ c) h`. Establish `h3` using `FF_FFStar_ram q hχ h`. Rewrite `h3` using `[FF_eq_D_Gs_of_mem_Mram q h2, FFStar_eq_U_GsStar q χ h, hGsU, ← Module.End.mul_apply (Gs χ), Gs_mul_GsStar hχ]`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hN, sub_zero, map_smul] at h3`.

Conclude with `eq_zpow_smul h3`.
-/
theorem D_U_ram [Fintype n] (hχ : χ ≠ 1) {φ : Form k n M} (h : φ ∈ Mram k n M) :
    D q (U q φ) = ((resCard k : ℂ) ^ ((Fintype.card n : ℤ) - 1)) • φ := by
  have hGsU : ∀ ψ : Form k n M, Gs χ (U q ψ) = U q (Gs χ ψ) := fun ψ => by
    have e : (Gs χ * U q : Module.End ℂ (Form k n M)) = U q * Gs χ := by
      unfold Gs
      exact (commute_sum (fun c => U_dia q c) _ (fun d : 𝓀[k]ˣ => χ d) fun d => d).symm
    exact LinearMap.congr_fun e ψ
  have hN : Nm φ = 0 := h
  have h2 : FFStar q χ φ ∈ Mram k n M := mem_ram (fun c => FFStar_dia q χ c) h
  have h3 := FF_FFStar_ram q hχ h
  rw [FF_eq_D_Gs_of_mem_Mram q h2, FFStar_eq_U_GsStar q χ h, hGsU, ← Module.End.mul_apply (Gs χ),
    Gs_mul_GsStar hχ] at h3
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hN, sub_zero, map_smul] at h3
  exact eq_zpow_smul h3

/- English proof (translation)
Establish `hGsD : ∀ ψ : Form k n M, GsStar χ (D q ψ) = D q (GsStar χ ψ)` using `fun ψ => by`. Establish `e : (GsStar χ * D q : Module.End ℂ (Form k n M)) = D q * GsStar χ`. Unfold `GsStar`. Conclude with `(commute_sum (fun c => D_dia q c) _ (fun d : 𝓀[k]ˣ => χ (-(d : 𝓀[k]))) fun d => d⁻¹).symm`. Conclude with `LinearMap.congr_fun e ψ`.

Establish `hN : Nm φ = 0` using `h`. Establish `h2 : FF q χ φ ∈ Mram k n M` using `mem_ram (fun c => FF_dia q χ c) h`. Establish `h3` using `FFStar_FF_ram q hχ h`. Rewrite `h3` using `[FFStar_eq_U_GsStar q χ h2, FF_eq_D_Gs_of_mem_Mram q h, hGsD, ← Module.End.mul_apply (GsStar χ), GsStar_mul_Gs hχ]`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hN, sub_zero, map_smul] at h3`.

Conclude with `eq_zpow_smul h3`.
-/
theorem U_D_ram [Fintype n] (hχ : χ ≠ 1) {φ : Form k n M} (h : φ ∈ Mram k n M) :
    U q (D q φ) = ((resCard k : ℂ) ^ ((Fintype.card n : ℤ) - 1)) • φ := by
  have hGsD : ∀ ψ : Form k n M, GsStar χ (D q ψ) = D q (GsStar χ ψ) := fun ψ => by
    have e : (GsStar χ * D q : Module.End ℂ (Form k n M)) = D q * GsStar χ := by
      unfold GsStar
      exact (commute_sum (fun c => D_dia q c) _ (fun d : 𝓀[k]ˣ => χ (-(d : 𝓀[k]))) fun d => d⁻¹).symm
    exact LinearMap.congr_fun e ψ
  have hN : Nm φ = 0 := h
  have h2 : FF q χ φ ∈ Mram k n M := mem_ram (fun c => FF_dia q χ c) h
  have h3 := FFStar_FF_ram q hχ h
  rw [FFStar_eq_U_GsStar q χ h2, FF_eq_D_Gs_of_mem_Mram q h, hGsD, ← Module.End.mul_apply (GsStar χ),
    GsStar_mul_Gs hχ] at h3
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hN, sub_zero, map_smul] at h3
  exact eq_zpow_smul h3

variable (χ) in

/- English proof (translation)
Rewrite using `[← FFStar_dia q χ c, mul_assoc, ← mul_assoc (dia c), ← map_mul, mul_inv_cancel, map_one, one_mul]`.
-/
theorem unit_FFStar_FF (c : 𝓀[k]ˣ) :
    (dia c * FFStar q χ * (dia c⁻¹ * FF q χ) : Module.End ℂ (Form k n M)) = FFStar q χ * FF q χ := by
  rw [← FFStar_dia q χ c, mul_assoc, ← mul_assoc (dia c), ← map_mul, mul_inv_cancel, map_one, one_mul]

variable (χ) in

/- English proof (translation)
Rewrite using `[← FF_dia q χ c⁻¹, mul_assoc, ← mul_assoc (dia c⁻¹), ← map_mul, inv_mul_cancel, map_one, one_mul]`.
-/
theorem unit_FF_FFStar (c : 𝓀[k]ˣ) :
    (dia c⁻¹ * FF q χ * (dia c * FFStar q χ) : Module.End ℂ (Form k n M)) = FF q χ * FFStar q χ := by
  rw [← FF_dia q χ c⁻¹, mul_assoc, ← mul_assoc (dia c⁻¹), ← map_mul, inv_mul_cancel, map_one, one_mul]

/- English proof (translation)
Rewrite using `[FFStar_apply, ofDual_lat, sum_withKer L q]`. Simplify using `only [cross_up_ofDual]`. Use `FFStar_mul_FF := LinearMap.ext fun φ => by`. Rewrite using `[Module.End.mul_apply, Model.FFStar_FF q hχ φ]`. Simplify using the standard rewrite rules.

Use `FF_mul_FFStar := LinearMap.ext fun φ => by`. Rewrite using `[Module.End.mul_apply, FF_FFStar q hχ φ]`. Simplify using the standard rewrite rules. Use `FFStar_FF_ram φ h := FFStar_FF_ram q hχ h`. Use `FF_FFStar_ram φ h := FF_FFStar_ram q hχ h`.

Use `FF_mem_ram φ h := mem_ram (fun c => FF_dia q χ c) h`. Use `FFStar_mem_ram φ h := mem_ram (fun c => FFStar_dia q χ c) h`. Use `D_dia c := D_dia q c`. Use `FF_dia c := FF_dia q χ c`. Use `FF_eq_D_Gs φ h := FF_eq_D_Gs_of_mem_Mram q h`.

Use `Gs_mul_GsStar := Gs_mul_GsStar hχ`. Use `D_U_ram φ h := D_U_ram q hχ h`. Use `U_D_ram φ h := U_D_ram q hχ h`. Use `FFStar_dia c := FFStar_dia q χ c`. Use `U_dia c := U_dia q c`.

Use `dia_mem_ram c φ h := mem_ram (fun d => dia_dia c d) h`. Use `phiOne_dia c m _ P Q := by`. Use function extensionality and compare the values at `x`. Unfold `phiOne`. Distinguish the cases in `hM : Maps P Q x`.

Rewrite using `[if_pos hM, if_pos ((maps_dia c).mpr hM)]`. Rewrite using `[if_neg hM, if_neg fun h' => hM ((maps_dia c).mp h')]`. Use `twisted_class_sum ε φ L _ _ f := by`. Rewrite using `[dia_apply, smul_ofDual, FFStar_ofDual]`. Simplify using `[LinearMap.smul_apply]`.

Use `sign_FFStar_sign_FF := by`. Establish `e` using `unit_FFStar_FF (n := n) (M := M) q χ (-1)`. Establish `hm : ((-1 : 𝓀[k]ˣ))⁻¹ = -1` using `by simp`. Rewrite `e` using `[hm]`. Conclude with `e`.

Use `sign_ram φ h := by`. Establish `e` using `LinearMap.congr_fun (unit_FFStar_FF q χ (-1)) φ`. Establish `hm : ((-1 : 𝓀[k]ˣ))⁻¹ = -1` using `by simp`. Rewrite `e` using `[hm]`. Simplify using `only [Module.End.mul_apply] at e`.

Rewrite using `[e, FFStar_FF_ram q hχ h]`. Use `unit_ram c φ h := by`. Establish `e` using `LinearMap.congr_fun (unit_FFStar_FF q χ c) φ`. Simplify using `only [Module.End.mul_apply] at e`. Rewrite using `[e, FFStar_FF_ram q hχ h]`.
-/
theorem operatorIdentities [Fintype n] (hχ : χ ≠ 1) : OperatorIdentities k n M q χ where
  FFStar_formula φ L _ _ f := by
    rw [FFStar_apply, ofDual_lat, sum_withKer L q]
    simp only [cross_up_ofDual]
  FFStar_mul_FF := LinearMap.ext fun φ => by
    rw [Module.End.mul_apply, Model.FFStar_FF q hχ φ]
    simp
  FF_mul_FFStar := LinearMap.ext fun φ => by
    rw [Module.End.mul_apply, FF_FFStar q hχ φ]
    simp
  FFStar_FF_ram φ h := FFStar_FF_ram q hχ h
  FF_FFStar_ram φ h := FF_FFStar_ram q hχ h
  FF_mem_ram φ h := mem_ram (fun c => FF_dia q χ c) h
  FFStar_mem_ram φ h := mem_ram (fun c => FFStar_dia q χ c) h
  D_dia c := D_dia q c
  FF_dia c := FF_dia q χ c
  FF_eq_D_Gs φ h := FF_eq_D_Gs_of_mem_Mram q h
  Gs_mul_GsStar := Gs_mul_GsStar hχ
  D_U_ram φ h := D_U_ram q hχ h
  U_D_ram φ h := U_D_ram q hχ h
  FFStar_dia c := FFStar_dia q χ c
  U_dia c := U_dia q c
  dia_mem_ram c φ h := mem_ram (fun d => dia_dia c d) h
  phiOne_dia c m _ P Q := by
    funext x
    unfold phiOne
    by_cases hM : Maps P Q x
    · rw [if_pos hM, if_pos ((maps_dia c).mpr hM)]
    · rw [if_neg hM, if_neg fun h' => hM ((maps_dia c).mp h')]
  twisted_class_sum ε φ L _ _ f := by
    rw [dia_apply, smul_ofDual, FFStar_ofDual]
    simp [LinearMap.smul_apply]
  sign_FFStar_sign_FF := by
    have e := unit_FFStar_FF (n := n) (M := M) q χ (-1)
    have hm : ((-1 : 𝓀[k]ˣ))⁻¹ = -1 := by simp
    rw [hm] at e
    exact e
  sign_ram φ h := by
    have e := LinearMap.congr_fun (unit_FFStar_FF q χ (-1)) φ
    have hm : ((-1 : 𝓀[k]ˣ))⁻¹ = -1 := by simp
    rw [hm] at e
    simp only [Module.End.mul_apply] at e
    rw [e, FFStar_FF_ram q hχ h]
  unit_ram c φ h := by
    have e := LinearMap.congr_fun (unit_FFStar_FF q χ c) φ
    simp only [Module.End.mul_apply] at e
    rw [e, FFStar_FF_ram q hχ h]

section Adjoint
variable {A B A' B' : Module.End ℂ (Form k n ℂ)}

/- English proof (translation)
Introduce `φ hφ`. Use `(hφ.biUnion fun Q _ => (S' Q).finite_toSet).subset ?_` and prove the remaining obligations. Introduce `P hP`. Rewrite `hP` using `[Function.mem_support, sumOp_apply]`. Take `⟨Q, hQ, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hP`.

Conclude with `Set.mem_biUnion (x := Q) (Function.mem_support.mpr fun h0 => hne (by rw [h0, smul_zero])) (Finset.mem_coe.mpr (hS P Q hQ))`.
-/
theorem keepsFinite_sumOp (S S' : Pair k n → Finset (Pair k n)) (w : Pair k n → Pair k n → ℂ)
    (hS : ∀ P Q, Q ∈ S P → P ∈ S' Q) : KeepsFinite (sumOp S w) := by
  intro φ hφ
  refine (hφ.biUnion fun Q _ => (S' Q).finite_toSet).subset ?_
  intro P hP
  rw [Function.mem_support, sumOp_apply] at hP
  obtain ⟨Q, hQ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
  exact Set.mem_biUnion (x := Q) (Function.mem_support.mpr fun h0 => hne (by rw [h0, smul_zero]))
    (Finset.mem_coe.mpr (hS P Q hQ))

/- English proof (translation)
Introduce `φ hφ`. Establish `e : Function.support (dia c φ) = (fun P => c • P) ⁻¹' Function.support φ`. Use extensionality with `P`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Conclude with `hφ.preimage (MulAction.injective c).injOn`.
-/
theorem keepsFinite_dia (c : 𝓀[k]ˣ) : KeepsFinite (n := n) (dia c) := by
  intro φ hφ
  have e : Function.support (dia c φ) = (fun P => c • P) ⁻¹' Function.support φ := by
    ext P
    simp
  rw [e]
  exact hφ.preimage (MulAction.injective c).injOn

/- English proof (translation)
Introduce `φ hφ`. Rewrite using `[Module.End.mul_apply]`. Conclude with `hA _ (hB φ hφ)`.
-/
theorem keepsFinite_mul (hA : KeepsFinite A) (hB : KeepsFinite B) : KeepsFinite (A * B) := by
  intro φ hφ
  rw [Module.End.mul_apply]
  exact hA _ (hB φ hφ)

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Simplify using `[ha]`. Distinguish the cases in `hf : (Function.support f).Finite`. Conclude with `(mul_finsum f a).symm`. Rewrite using `[finsum_of_infinite_support hf, mul_zero]`.

Conclude with `finsum_of_infinite_support fun h => hf (h.subset fun i hi => mul_ne_zero ha hi)`.
-/
private theorem finsum_const_mul_eq_mul_finsum {ι : Type} (a : ℂ) (f : ι → ℂ) : ∑ᶠ i, a * f i = a * ∑ᶠ i, f i := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hf : (Function.support f).Finite
  · exact (mul_finsum f a).symm
  · rw [finsum_of_infinite_support hf, mul_zero]
    exact finsum_of_infinite_support fun h => hf (h.subset fun i hi => mul_ne_zero ha hi)

/- English proof (translation)
Unfold `cntIp`. Rewrite using `[← finsum_const_mul_eq_mul_finsum]`. Conclude with `finsum_congr fun P => by simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring`.
-/
theorem cntIp_smul_right (a : ℂ) (φ φ' : Form k n ℂ) : cntIp φ (a • φ') = (starRingEnd ℂ) a * cntIp φ φ' := by
  unfold cntIp
  rw [← finsum_const_mul_eq_mul_finsum]
  exact finsum_congr fun P => by simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring

/- English proof (translation)
Unfold `cntIp`. Rewrite using `[← finsum_const_mul_eq_mul_finsum]`. Conclude with `finsum_congr fun P => by simp only [Pi.smul_apply, smul_eq_mul]; ring`.
-/
theorem cntIp_smul_left (a : ℂ) (φ φ' : Form k n ℂ) : cntIp (a • φ) φ' = a * cntIp φ φ' := by
  unfold cntIp
  rw [← finsum_const_mul_eq_mul_finsum]
  exact finsum_congr fun P => by simp only [Pi.smul_apply, smul_eq_mul]; ring

/- English proof (translation)
Introduce `φ φ' hφ hφ'`. Simplify using `only [Module.End.mul_apply]`. Rewrite using `[h _ _ (hB φ hφ) hφ', h' _ _ hφ (hA φ' hφ')]`.
-/
theorem isAdj_mul (h : IsAdj A A') (h' : IsAdj B B') (hB : KeepsFinite B) (hA : KeepsFinite A') :
    IsAdj (A * B) (B' * A') := by
  intro φ φ' hφ hφ'
  simp only [Module.End.mul_apply]
  rw [h _ _ (hB φ hφ) hφ', h' _ _ hφ (hA φ' hφ')]

/- English proof (translation)
Unfold `cntIp`. Use `finsum_eq_sum_of_support_subset _ fun P hP => ?_` and prove the remaining obligations. Rewrite `hP` using `[Function.mem_support]`. Break down `hs with hs | hs` into its components or cases. Conclude with `hs (Function.mem_support.mpr fun h0 => hP (by rw [h0]; simp))`.

Conclude with `hs (Function.mem_support.mpr fun h0 => hP (by rw [h0]; simp))`.
-/
private theorem cntIp_eq_sum_of_support_subset (φ φ' : Form k n ℂ) (s : Finset (Pair k n))
    (hs : Function.support φ' ⊆ s ∨ Function.support φ ⊆ s) :
    cntIp φ φ' = ∑ P ∈ s, φ P * (starRingEnd ℂ) (φ' P) := by
  unfold cntIp
  refine finsum_eq_sum_of_support_subset _ fun P hP => ?_
  rw [Function.mem_support] at hP
  rcases hs with hs | hs
  · exact hs (Function.mem_support.mpr fun h0 => hP (by rw [h0]; simp))
  · exact hs (Function.mem_support.mpr fun h0 => hP (by rw [h0]; simp))

/- English proof (translation)
Rewrite using `[cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inl (by simp)), cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inl (by simp)), cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inl (by simp)), ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun P _ => by rw [Pi.add_apply, add_mul]`.
-/
private theorem cntIp_add_left (φ₁ φ₂ φ' : Form k n ℂ) (h : (Function.support φ').Finite) :
    cntIp (φ₁ + φ₂) φ' = cntIp φ₁ φ' + cntIp φ₂ φ' := by
  rw [cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inl (by simp)), cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inl (by simp)),
    cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inl (by simp)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun P _ => by rw [Pi.add_apply, add_mul]

/- English proof (translation)
Rewrite using `[cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inr (by simp)), cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inr (by simp)), cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inr (by simp)), ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun P _ => by rw [Pi.add_apply, map_add, mul_add]`.
-/
private theorem cntIp_add_right (φ φ₁ φ₂ : Form k n ℂ) (h : (Function.support φ).Finite) :
    cntIp φ (φ₁ + φ₂) = cntIp φ φ₁ + cntIp φ φ₂ := by
  rw [cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inr (by simp)), cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inr (by simp)),
    cntIp_eq_sum_of_support_subset _ _ h.toFinset (Or.inr (by simp)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun P _ => by rw [Pi.add_apply, map_add, mul_add]

/- English proof (translation)
Introduce `φ φ' hφ hφ'`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [cntIp]`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj, Finset.sum_insert hj, LinearMap.add_apply, LinearMap.add_apply, cntIp_add_left _ _ _ hφ', cntIp_add_right _ _ _ hφ, ih, LinearMap.smul_apply, LinearMap.smul_apply, cntIp_smul_left, cntIp_smul_right, h j φ φ' hφ hφ', hab j]`.
-/
theorem isAdj_sum {ι : Type} (s : Finset ι) (a b : ι → ℂ) (A B : ι → Module.End ℂ (Form k n ℂ))
    (hab : ∀ i, (starRingEnd ℂ) (b i) = a i) (h : ∀ i, IsAdj (A i) (B i)) :
    IsAdj (∑ i ∈ s, a i • A i) (∑ i ∈ s, b i • B i) := by
  classical
  intro φ φ' hφ hφ'
  induction s using Finset.induction_on with
  | empty => simp [cntIp]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, LinearMap.add_apply, LinearMap.add_apply,
      cntIp_add_left _ _ _ hφ', cntIp_add_right _ _ _ hφ, ih, LinearMap.smul_apply, LinearMap.smul_apply,
      cntIp_smul_left, cntIp_smul_right, h j φ φ' hφ hφ', hab j]

/- English proof (translation)
Introduce `φ φ' _ _`. Unfold `cntIp`. Simplify using `only [dia_apply]`. Use `conv_rhs => rw [← finsum_comp_equiv (MulAction.toPerm c : Equiv.Perm (Pair k n))]`. Simplify using `[MulAction.toPerm_apply]`.
-/
theorem isAdj_dia (c : 𝓀[k]ˣ) : IsAdj (n := n) (dia c) (dia c⁻¹) := by
  intro φ φ' _ _
  unfold cntIp
  simp only [dia_apply]
  conv_rhs => rw [← finsum_comp_equiv (MulAction.toPerm c : Equiv.Perm (Pair k n))]
  simp [MulAction.toPerm_apply]

/- English proof (translation)
Use `⟨⟨fun φ hφ => ⟨hAW φ hφ.1, hA φ hφ.2⟩, fun φ hφ φ' hφ' e => ?_, fun φ hφ => ?_⟩, fun φ hφ φ' hφ' hf hf' => ?_⟩` and prove the remaining obligations. Use `congrArg B e` as an intermediate fact. Rewrite `this` using `[hBA φ hφ.1, hBA φ' hφ'.1]`. Conclude with `smul_right_injective _ ha this`. Use `⟨a⁻¹ • B φ, ⟨W.smul_mem _ (hBW φ hφ.1), ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `(hB φ hφ.2).subset (Function.support_const_smul_subset _ _)`. Rewrite using `[map_smul, hAB φ hφ.1, smul_smul, inv_mul_cancel₀ ha, one_smul]`. Rewrite using `[h _ _ hf (hA φ' hf'), hBA φ' hφ', cntIp_smul_right, ha']`.
-/
theorem isScaledUnitaryOn {W : Submodule ℂ (Form k n ℂ)} {a : ℂ} (ha : a ≠ 0) (ha' : (starRingEnd ℂ) a = a)
    (hA : KeepsFinite A) (hB : KeepsFinite B) (hAW : ∀ φ ∈ W, A φ ∈ W) (hBW : ∀ φ ∈ W, B φ ∈ W) (h : IsAdj A B)
    (hBA : ∀ φ ∈ W, B (A φ) = a • φ) (hAB : ∀ φ ∈ W, A (B φ) = a • φ) : IsScaledUnitaryOn W a A := by
  refine ⟨⟨fun φ hφ => ⟨hAW φ hφ.1, hA φ hφ.2⟩, fun φ hφ φ' hφ' e => ?_, fun φ hφ => ?_⟩,
    fun φ hφ φ' hφ' hf hf' => ?_⟩
  · have := congrArg B e
    rw [hBA φ hφ.1, hBA φ' hφ'.1] at this
    exact smul_right_injective _ ha this
  · refine ⟨a⁻¹ • B φ, ⟨W.smul_mem _ (hBW φ hφ.1), ?_⟩, ?_⟩
    · exact (hB φ hφ.2).subset (Function.support_const_smul_subset _ _)
    · rw [map_smul, hAB φ hφ.1, smul_smul, inv_mul_cancel₀ ha, one_smul]
  · rw [h _ _ hf (hA φ' hf'), hBA φ' hφ', cntIp_smul_right, ha']

/- English proof (translation)
Establish `hinv : ∀ d : 𝓀[k]ˣ, ∀ φ : Form k n ℂ, dia d⁻¹ (dia d φ) = φ` using `fun d φ => by`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Use `⟨⟨fun φ hφ => ⟨hW c φ hφ.1, keepsFinite_dia c φ hφ.2⟩, fun φ _ φ' _ e => ?_, fun φ hφ => ?_⟩, fun φ _ φ' _ hf hf' => ?_⟩` and prove the remaining obligations. Rewrite using `[← hinv c φ, e, hinv c φ']`. Use `⟨dia c⁻¹ φ, ⟨hW c⁻¹ φ hφ.1, keepsFinite_dia c⁻¹ φ hφ.2⟩, ?_⟩` and prove the remaining obligations.

Use `hinv c⁻¹ φ` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Rewrite using `[isAdj_dia c _ _ hf (keepsFinite_dia c φ' hf'), hinv c φ', one_mul]`.
-/
theorem dia_unitary {W : Submodule ℂ (Form k n ℂ)} (hW : ∀ c : 𝓀[k]ˣ, ∀ φ ∈ W, dia c φ ∈ W) (c : 𝓀[k]ˣ) :
    IsScaledUnitaryOn W 1 (dia c) := by
  have hinv : ∀ d : 𝓀[k]ˣ, ∀ φ : Form k n ℂ, dia d⁻¹ (dia d φ) = φ := fun d φ => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  refine ⟨⟨fun φ hφ => ⟨hW c φ hφ.1, keepsFinite_dia c φ hφ.2⟩, fun φ _ φ' _ e => ?_, fun φ hφ => ?_⟩,
    fun φ _ φ' _ hf hf' => ?_⟩
  · rw [← hinv c φ, e, hinv c φ']
  · refine ⟨dia c⁻¹ φ, ⟨hW c⁻¹ φ hφ.1, keepsFinite_dia c⁻¹ φ hφ.2⟩, ?_⟩
    have := hinv c⁻¹ φ
    rwa [inv_inv] at this
  · rw [isAdj_dia c _ _ hf (keepsFinite_dia c φ' hf'), hinv c φ', one_mul]

/- English proof (translation)
Establish `hχ : resChar ψ hψ q ≠ 1` using `resChar_ne_one hψ q`. Establish `hFF : KeepsFinite (n` using `n) (FF q (resChar ψ hψ q)) := by`. Unfold `FF`. Conclude with `keepsFinite_sumOp _ (fun Q => withKer Q.lat) _ fun P Q hQ => mem_withKer.mpr (mem_withLat.mp hQ).symm`. Establish `hFFS : KeepsFinite (n` using `n) (FFStar q (resChar ψ hψ q)) := by`.

Unfold `FFStar`. Conclude with `keepsFinite_sumOp _ (fun Q => withLat Q.ker) _ fun P Q hQ => mem_withLat.mpr (mem_withKer.mp hQ).symm`. Establish `hD : KeepsFinite (n` using `n) (D q) := by`. Unfold `D Da`. Conclude with `keepsFinite_sumOp _ (fun Q => withKer Q.lat) _ fun P Q hQ => mem_withKer.mpr (mem_withLat.mp (Finset.mem_filter.mp hQ).1).symm`.

Establish `hU : KeepsFinite (n` using `n) (U q) := by`. Unfold `U`. Conclude with `keepsFinite_sumOp _ (fun Q => withLat Q.ker) _ fun P Q hQ => mem_withLat.mpr (mem_withKer.mp (Finset.mem_filter.mp hQ).1).symm`. Establish `hadj : IsAdj (n` using `n) (FF q (resChar ψ hψ q)) (FFStar q (resChar ψ hψ q)) := by`. Unfold `FF FFStar`.

Use `Model.isAdj_sumOp _ _ _ _ (fun P Q => ?_) fun P Q _ => ?_` and prove the remaining obligations. Simplify using `only [mem_withLat, mem_withKer]`. Conclude with `eq_comm`. Rewrite using `[conj_resChar, neg_neg]`. Establish `hq : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0` using `pow_ne_zero _ resCard_ne_zero`.

Establish `hqr : (starRingEnd ℂ) ((resCard k : ℂ) ^ Fintype.card n) = (resCard k : ℂ) ^ Fintype.card n` using `by simp`. Establish `hram : ∀ c : 𝓀[k]ˣ, ∀ φ ∈ Mram k n ℂ, dia c φ ∈ Mram k n ℂ` using `fun c φ h => mem_ram (fun d => dia_dia c d) h`. Establish `hunit : ∀ c : 𝓀[k]ˣ, IsAdj (n` using `n) (dia c⁻¹ * FF q (resChar ψ hψ q)) (dia c * FFStar q (resChar ψ hψ q)) ∧ IsScaledUnitaryOn (Mram k n ℂ) ((resCard k : ℂ) ^ Fintype.card n) (dia c⁻¹ * FF q (resChar ψ hψ q)) := by`. Introduce `c`. Establish `hA : IsAdj (n` using `n) (dia c⁻¹ * FF q (resChar ψ hψ q)) (dia c * FFStar q (resChar ψ hψ q)) := by`.

Establish `e` using `isAdj_mul (isAdj_dia c⁻¹) hadj hFF (keepsFinite_dia _)`. Rewrite `e` using `[inv_inv, FFStar_dia]`. Then use the resulting hypothesis. Use `⟨hA, isScaledUnitaryOn hq hqr (keepsFinite_mul (keepsFinite_dia _) hFF) (keepsFinite_mul (keepsFinite_dia _) hFFS) (fun φ h => ?_) (fun φ h => ?_) hA (fun φ h => ?_) fun φ h => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.End.mul_apply]`. Conclude with `hram _ _ (mem_ram (fun d => FF_dia q _ d) h)`.

Rewrite using `[Module.End.mul_apply]`. Conclude with `hram _ _ (mem_ram (fun d => FFStar_dia q _ d) h)`. Establish `e` using `LinearMap.congr_fun (unit_FFStar_FF q (resChar ψ hψ q) c) φ`. Simplify using `only [Module.End.mul_apply] at e ⊢`. Rewrite using `[e, FFStar_FF_ram q hχ h]`.

Establish `e` using `LinearMap.congr_fun (unit_FF_FFStar q (resChar ψ hψ q) c) φ`. Simplify using `only [Module.End.mul_apply] at e ⊢`. Rewrite using `[e, FF_FFStar_ram q hχ h]`. Establish `hm : ((-1 : 𝓀[k]ˣ))⁻¹ = -1` using `by simp`. Use `⟨⟨hFF, hFFS⟩, ⟨hD, hU⟩, hadj, ?_, ?_, ?_, fun c => isAdj_dia c, fun c => ⟨dia_unitary (fun _ _ _ => Submodule.mem_top) c, dia_unitary hram c⟩, ?_, ?_, hunit⟩` and prove the remaining obligations.

Conclude with `isScaledUnitaryOn hq hqr hFF hFFS (fun φ h => mem_ram (fun d => FF_dia q _ d) h) (fun φ h => mem_ram (fun d => FFStar_dia q _ d) h) hadj (fun φ h => FFStar_FF_ram q hχ h) fun φ h => FF_FFStar_ram q hχ h`. Unfold `Gs GsStar`. Conclude with `isAdj_sum _ _ _ _ _ (fun c => by rw [conj_resChar, neg_neg]) fun c => isAdj_dia c`. Unfold `U D Da`. Use `Model.isAdj_sumOp _ _ _ _ (fun P Q => ?_) fun _ _ _ => by simp` and prove the remaining obligations.

Simplify using `only [Finset.mem_filter, mem_withKer, mem_withLat]`. Conclude with `and_congr eq_comm Iff.rfl`. Establish `e` using `(hunit (-1)).1`. Rewrite `e` using `[hm]`. Then use the resulting hypothesis. Establish `e` using `(hunit (-1)).2`.

Rewrite `e` using `[hm]`. Then use the resulting hypothesis.
-/
theorem adjointIdentities [Fintype n] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) :
    AdjointIdentities k n q (resChar ψ hψ q) := by
  classical
  have hχ : resChar ψ hψ q ≠ 1 := resChar_ne_one hψ q
  have hFF : KeepsFinite (n := n) (FF q (resChar ψ hψ q)) := by
    unfold FF
    exact keepsFinite_sumOp _ (fun Q => withKer Q.lat) _ fun P Q hQ =>
      mem_withKer.mpr (mem_withLat.mp hQ).symm
  have hFFS : KeepsFinite (n := n) (FFStar q (resChar ψ hψ q)) := by
    unfold FFStar
    exact keepsFinite_sumOp _ (fun Q => withLat Q.ker) _ fun P Q hQ =>
      mem_withLat.mpr (mem_withKer.mp hQ).symm
  have hD : KeepsFinite (n := n) (D q) := by
    unfold D Da
    exact keepsFinite_sumOp _ (fun Q => withKer Q.lat) _ fun P Q hQ =>
      mem_withKer.mpr (mem_withLat.mp (Finset.mem_filter.mp hQ).1).symm
  have hU : KeepsFinite (n := n) (U q) := by
    unfold U
    exact keepsFinite_sumOp _ (fun Q => withLat Q.ker) _ fun P Q hQ =>
      mem_withLat.mpr (mem_withKer.mp (Finset.mem_filter.mp hQ).1).symm
  have hadj : IsAdj (n := n) (FF q (resChar ψ hψ q)) (FFStar q (resChar ψ hψ q)) := by
    unfold FF FFStar
    refine Model.isAdj_sumOp _ _ _ _ (fun P Q => ?_) fun P Q _ => ?_
    · simp only [mem_withLat, mem_withKer]
      exact eq_comm
    · rw [conj_resChar, neg_neg]
  have hq : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ resCard_ne_zero
  have hqr : (starRingEnd ℂ) ((resCard k : ℂ) ^ Fintype.card n) = (resCard k : ℂ) ^ Fintype.card n := by simp
  have hram : ∀ c : 𝓀[k]ˣ, ∀ φ ∈ Mram k n ℂ, dia c φ ∈ Mram k n ℂ := fun c φ h =>
    mem_ram (fun d => dia_dia c d) h
  have hunit : ∀ c : 𝓀[k]ˣ, IsAdj (n := n) (dia c⁻¹ * FF q (resChar ψ hψ q)) (dia c * FFStar q (resChar ψ hψ q)) ∧
      IsScaledUnitaryOn (Mram k n ℂ) ((resCard k : ℂ) ^ Fintype.card n) (dia c⁻¹ * FF q (resChar ψ hψ q)) := by
    intro c
    have hA : IsAdj (n := n) (dia c⁻¹ * FF q (resChar ψ hψ q)) (dia c * FFStar q (resChar ψ hψ q)) := by
      have e := isAdj_mul (isAdj_dia c⁻¹) hadj hFF (keepsFinite_dia _)
      rwa [inv_inv, FFStar_dia] at e
    refine ⟨hA, isScaledUnitaryOn hq hqr (keepsFinite_mul (keepsFinite_dia _) hFF)
      (keepsFinite_mul (keepsFinite_dia _) hFFS) (fun φ h => ?_) (fun φ h => ?_) hA (fun φ h => ?_) fun φ h => ?_⟩
    · rw [Module.End.mul_apply]
      exact hram _ _ (mem_ram (fun d => FF_dia q _ d) h)
    · rw [Module.End.mul_apply]
      exact hram _ _ (mem_ram (fun d => FFStar_dia q _ d) h)
    · have e := LinearMap.congr_fun (unit_FFStar_FF q (resChar ψ hψ q) c) φ
      simp only [Module.End.mul_apply] at e ⊢
      rw [e, FFStar_FF_ram q hχ h]
    · have e := LinearMap.congr_fun (unit_FF_FFStar q (resChar ψ hψ q) c) φ
      simp only [Module.End.mul_apply] at e ⊢
      rw [e, FF_FFStar_ram q hχ h]
  have hm : ((-1 : 𝓀[k]ˣ))⁻¹ = -1 := by simp
  refine ⟨⟨hFF, hFFS⟩, ⟨hD, hU⟩, hadj, ?_, ?_, ?_, fun c => isAdj_dia c,
    fun c => ⟨dia_unitary (fun _ _ _ => Submodule.mem_top) c, dia_unitary hram c⟩, ?_, ?_, hunit⟩
  · exact isScaledUnitaryOn hq hqr hFF hFFS (fun φ h => mem_ram (fun d => FF_dia q _ d) h)
      (fun φ h => mem_ram (fun d => FFStar_dia q _ d) h) hadj (fun φ h => FFStar_FF_ram q hχ h)
      fun φ h => FF_FFStar_ram q hχ h
  · unfold Gs GsStar
    exact isAdj_sum _ _ _ _ _ (fun c => by rw [conj_resChar, neg_neg]) fun c => isAdj_dia c
  · unfold U D Da
    refine Model.isAdj_sumOp _ _ _ _ (fun P Q => ?_) fun _ _ _ => by simp
    simp only [Finset.mem_filter, mem_withKer, mem_withLat]
    exact and_congr eq_comm Iff.rfl
  · have e := (hunit (-1)).1
    rwa [hm] at e
  · have e := (hunit (-1)).2
    rwa [hm] at e

end Adjoint

/- English proof (translation)
Introduce `k _ _ _ _ ϖ ψ hψ n _ _`. Conclude with `⟨fun M _ _ => ⟨vanishing ϖ, operatorIdentities ϖ (resChar_ne_one hψ ϖ)⟩, adjointIdentities ϖ hψ⟩`.
-/
theorem pairOperatorStatement : PairOperatorStatement := by
  intro k _ _ _ _ ϖ ψ hψ n _ _
  exact ⟨fun M _ _ => ⟨vanishing ϖ, operatorIdentities ϖ (resChar_ne_one hψ ϖ)⟩, adjointIdentities ϖ hψ⟩

end GlobalTheory.PairOp
