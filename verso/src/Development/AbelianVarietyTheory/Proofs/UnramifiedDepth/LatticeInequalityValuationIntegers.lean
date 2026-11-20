import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.HasLenCokerDet
import ReciprocityTheory.DualLattices.ProdDvdOfIso
import ReciprocityTheory.DualLattices.ColengthSqBlockVandermonde

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

section aux

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

/- English proof (translation)
Establish `: IsDomain O` using `hv.hom_inj.isDomain`. Establish `: IsFractionRing O C` using `hv.isFractionRing`. Establish `: ValuationRing O` using `ValuationRing.of_integers v hv`. Establish `: Module.Finite O N` using `Module.Finite.iff_fg.2 hN`. Establish `: Module.Flat O N`.

Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]`. Use `infer_instance`. Establish `: Module.Free O N` using `Module.free_of_flat_of_isLocalRing`. Establish `h1 : Module.finrank O N ≤ Module.finrank O (κ → O)` using `LinearMap.finrank_le_finrank_of_injective (f := N.subtype) N.injective_subtype`. Establish `h2 : Module.finrank O (κ → O) ≤ Module.finrank O N`.

Use `LinearMap.finrank_le_finrank_of_injective (f := LinearMap.codRestrict N (D • LinearMap.id) (fun z => hDN z)) ?_` and prove the remaining obligations. Introduce `x y hxy`. Establish `h3 : D • x = D • y` using `congrArg Subtype.val hxy`. Use function extensionality and compare the values at `i`. Conclude with `mul_left_cancel₀ hD (congrFun h3 i)`.

Establish `h3 : Module.finrank O N = Fintype.card κ`. Rewrite using `[← Module.finrank_fintype_fun_eq_card O]`. Use linear arithmetic over natural numbers and integers. Set `b : Module.Basis κ O N` to `(Module.finBasisOfFinrankEq O N h3).reindex (Fintype.equivFin κ).symm`. Establish `hB : ∀ c : κ → O, (Matrix.of fun i j => (b j : κ → O) i) *ᵥ c = ((∑ j, c j • b j : N) : κ → O)`.

Introduce `c`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`. Use `⟨Matrix.of fun i j => (b j : κ → O) i, ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Take `⟨c, hc, hc0⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Rewrite `hc0` using `[hB]`. Establish `h4 : (∑ j, c j • b j : N) = 0` using `Subtype.ext hc0`. Conclude with `hc (funext (Fintype.linearIndependent_iff.1 b.linearIndependent c h4))`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Rewrite using `[Matrix.mulVecLin_apply, hB]`. Conclude with `Subtype.property _`. Introduce `hx`.

Use `⟨b.repr ⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVecLin_apply, hB, b.sum_repr]`.
-/
private theorem exists_basisMat (hv : v.Integers O) {κ : Type} [Fintype κ] [DecidableEq κ]
    (N : Submodule O (κ → O)) (hN : N.FG) (D : O) (hD : D ≠ 0) (hDN : ∀ z, D • z ∈ N) :
    ∃ B : Matrix κ κ O, B.det ≠ 0 ∧ LinearMap.range B.mulVecLin = N := by
  have : IsDomain O := hv.hom_inj.isDomain
  have : IsFractionRing O C := hv.isFractionRing
  have : ValuationRing O := ValuationRing.of_integers v hv
  have : Module.Finite O N := Module.Finite.iff_fg.2 hN
  have : Module.Flat O N := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  have : Module.Free O N := Module.free_of_flat_of_isLocalRing
  have h1 : Module.finrank O N ≤ Module.finrank O (κ → O) :=
    LinearMap.finrank_le_finrank_of_injective (f := N.subtype) N.injective_subtype
  have h2 : Module.finrank O (κ → O) ≤ Module.finrank O N := by
    refine LinearMap.finrank_le_finrank_of_injective
      (f := LinearMap.codRestrict N (D • LinearMap.id) (fun z => hDN z)) ?_
    intro x y hxy
    have h3 : D • x = D • y := congrArg Subtype.val hxy
    funext i
    exact mul_left_cancel₀ hD (congrFun h3 i)
  have h3 : Module.finrank O N = Fintype.card κ := by
    rw [← Module.finrank_fintype_fun_eq_card O]; omega
  let b : Module.Basis κ O N :=
    (Module.finBasisOfFinrankEq O N h3).reindex (Fintype.equivFin κ).symm
  have hB : ∀ c : κ → O, (Matrix.of fun i j => (b j : κ → O) i) *ᵥ c =
      ((∑ j, c j • b j : N) : κ → O) := by
    intro c
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  refine ⟨Matrix.of fun i j => (b j : κ → O) i, ?_, ?_⟩
  · intro h0
    obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    rw [hB] at hc0
    have h4 : (∑ j, c j • b j : N) = 0 := Subtype.ext hc0
    exact hc (funext (Fintype.linearIndependent_iff.1 b.linearIndependent c h4))
  · ext x
    constructor
    · rintro ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, hB]
      exact Subtype.property _
    · intro hx
      refine ⟨b.repr ⟨x, hx⟩, ?_⟩
      rw [Matrix.mulVecLin_apply, hB, b.sum_repr]

/- English proof (translation)
Establish `h` using `RingHom.map_det (algebraMap O C) B`. Rewrite `h` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← h]`. Conclude with `fun h0 => hB (hv.hom_inj (by rw [h0, map_zero]))`.
-/
private theorem det_map_ne (hv : v.Integers O) {κ : Type} [Fintype κ] [DecidableEq κ]
    {B : Matrix κ κ O} (hB : B.det ≠ 0) : (B.map (algebraMap O C)).det ≠ 0 := by
  have h := RingHom.map_det (algebraMap O C) B
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  exact fun h0 => hB (hv.hom_inj (by rw [h0, map_zero]))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hc choose c₀ hc₀ using fun j => hv.exists_of_le_one (hc j)`. Conclude with `⟨c₀, funext fun j => (hc₀ j).symm⟩`. Introduce and unpack `⟨c₀, rfl⟩ j`. Conclude with `hv.map_le_one _`.
-/
private theorem integral_iff (hv : v.Integers O) {κ : Type} (c : κ → C) :
    (∀ j, v (c j) ≤ 1) ↔ ∃ c₀ : κ → O, c = fun j => algebraMap O C (c₀ j) := by
  constructor
  · intro hc
    choose c₀ hc₀ using fun j => hv.exists_of_le_one (hc j)
    exact ⟨c₀, funext fun j => (hc₀ j).symm⟩
  · rintro ⟨c₀, rfl⟩ j
    exact hv.map_le_one _

/- English proof (translation)
Establish `key : ∀ c₀ : κ → O, L.B *ᵥ (fun j => algebraMap O C (c₀ j)) = fun j => algebraMap O C ((B *ᵥ c₀) j)`. Introduce `c₀`. Use function extensionality and compare the values at `i`. Simplify using `[hL, Matrix.mulVec, dotProduct]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, hc, rfl⟩`. Take `⟨c₀, rfl⟩` from `(integral_iff hv c).1 hc`. Conclude with `⟨B *ᵥ c₀, ⟨c₀, rfl⟩, key c₀⟩`. Introduce and unpack `⟨_, ⟨c₀, rfl⟩, rfl⟩`. Conclude with `⟨_, (integral_iff hv _).2 ⟨c₀, rfl⟩, (key c₀).symm⟩`.
-/
private theorem mem_pts (hv : v.Integers O) {κ : Type} [Fintype κ] [DecidableEq κ]
    {B : Matrix κ κ O} (L : Lat v κ) (hL : L.B = B.map (algebraMap O C)) (x : κ → C) :
    x ∈ L.pts ↔ ∃ z ∈ LinearMap.range B.mulVecLin, x = fun j => algebraMap O C (z j) := by
  have key : ∀ c₀ : κ → O, L.B *ᵥ (fun j => algebraMap O C (c₀ j)) =
      fun j => algebraMap O C ((B *ᵥ c₀) j) := by
    intro c₀
    funext i
    simp [hL, Matrix.mulVec, dotProduct]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨c₀, rfl⟩ := (integral_iff hv c).1 hc
    exact ⟨B *ᵥ c₀, ⟨c₀, rfl⟩, key c₀⟩
  · rintro ⟨_, ⟨c₀, rfl⟩, rfl⟩
    exact ⟨_, (integral_iff hv _).2 ⟨c₀, rfl⟩, (key c₀).symm⟩

/- English proof (translation)
Establish `: IsDomain O` using `hv.hom_inj.isDomain`. Substitute `hM hM'` using the available equality. Establish `hcol : ∀ j, ∃ x : κ → O, B *ᵥ x = B' *ᵥ Pi.single j 1` using `fun j => hle ⟨Pi.single j 1, rfl⟩`. Use `choose X hX using hcol`. Establish `hBX : B * (Matrix.of X)ᵀ = B'`.

Use extensionality with `i j`. Use `congrFun (hX j) i` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hinj : Function.Injective B.mulVecLin`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `m hm`. Assume the negation of the conclusion as `h0`. Conclude with `hB (Matrix.exists_mulVec_eq_zero_iff.1 ⟨m, h0, hm⟩)`. Set `e` to `LinearEquiv.ofInjective B.mulVecLin hinj`. Establish `hmap : (LinearMap.range ((Matrix.of X)ᵀ).mulVecLin).map (e : (κ → O) →ₗ[O] LinearMap.range B.mulVecLin) = (LinearMap.range B'.mulVecLin).comap (LinearMap.range B.mulVecLin).subtype`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨w, rfl⟩, rfl⟩`. Use `⟨w, ?_⟩` and prove the remaining obligations. Use `show B' *ᵥ w = B *ᵥ ((Matrix.of X)ᵀ *ᵥ w)`.

Rewrite using `[Matrix.mulVec_mulVec, hBX]`. Introduce and unpack `⟨w, hw⟩`. Use `⟨_, ⟨w, rfl⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show B *ᵥ ((Matrix.of X)ᵀ *ᵥ w) = _`. Rewrite using `[Matrix.mulVec_mulVec, hBX]`.

Conclude with `hw`. Establish `h1` using `hasLen_of_equiv (Submodule.Quotient.equiv _ _ e hmap) hc`. Establish `h2` using `hasLen_unique hv h1 (hasLen_coker_det' v O hv κ _)`. Establish `h3 : v (B.map (algebraMap O C)).det ≠ 0` using `(Valuation.ne_zero_iff v).2 (det_map_ne hv hB)`. Establish `h4` using `RingHom.map_det (algebraMap O C) ((Matrix.of X)ᵀ)`.

Rewrite `h4` using `[RingHom.mapMatrix_apply]`. Rewrite using `[h2, ← hBX, Matrix.map_mul, Matrix.det_mul, map_mul, h4, mul_div_cancel_left₀ _ h3]`.
-/
private theorem len_eq (hv : v.Integers O) {κ : Type} [Fintype κ] [DecidableEq κ]
    {B B' : Matrix κ κ O} (hB : B.det ≠ 0) (M M' : Submodule O (κ → O))
    (hM : LinearMap.range B.mulVecLin = M) (hM' : LinearMap.range B'.mulVecLin = M')
    (hle : M' ≤ M) {c : NNReal} (hc : HasLen v O (M ⧸ M'.comap M.subtype) c) :
    c = v (B'.map (algebraMap O C)).det / v (B.map (algebraMap O C)).det := by
  have : IsDomain O := hv.hom_inj.isDomain
  subst hM hM'
  have hcol : ∀ j, ∃ x : κ → O, B *ᵥ x = B' *ᵥ Pi.single j 1 := fun j =>
    hle ⟨Pi.single j 1, rfl⟩
  choose X hX using hcol
  have hBX : B * (Matrix.of X)ᵀ = B' := by
    ext i j
    have := congrFun (hX j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have hinj : Function.Injective B.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    by_contra h0
    exact hB (Matrix.exists_mulVec_eq_zero_iff.1 ⟨m, h0, hm⟩)
  let e := LinearEquiv.ofInjective B.mulVecLin hinj
  have hmap : (LinearMap.range ((Matrix.of X)ᵀ).mulVecLin).map
      (e : (κ → O) →ₗ[O] LinearMap.range B.mulVecLin) =
      (LinearMap.range B'.mulVecLin).comap (LinearMap.range B.mulVecLin).subtype := by
    ext y
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      refine ⟨w, ?_⟩
      show B' *ᵥ w = B *ᵥ ((Matrix.of X)ᵀ *ᵥ w)
      rw [Matrix.mulVec_mulVec, hBX]
    · rintro ⟨w, hw⟩
      refine ⟨_, ⟨w, rfl⟩, Subtype.ext ?_⟩
      show B *ᵥ ((Matrix.of X)ᵀ *ᵥ w) = _
      rw [Matrix.mulVec_mulVec, hBX]
      exact hw
  have h1 := hasLen_of_equiv (Submodule.Quotient.equiv _ _ e hmap) hc
  have h2 := hasLen_unique hv h1 (hasLen_coker_det' v O hv κ _)
  have h3 : v (B.map (algebraMap O C)).det ≠ 0 := (Valuation.ne_zero_iff v).2 (det_map_ne hv hB)
  have h4 := RingHom.map_det (algebraMap O C) ((Matrix.of X)ᵀ)
  rw [RingHom.mapMatrix_apply] at h4
  rw [h2, ← hBX, Matrix.map_mul, Matrix.det_mul, map_mul, h4, mul_div_cancel_left₀ _ h3]

omit [Algebra O C] in

/- English proof (translation)
Establish `hprod : ∀ (S : Finset (Fin n)), ∀ f ∈ M, (fun y : Fin n × Fin s => (∏ σ ∈ S, (a y.1 - a σ)) * f y) ∈ M`. Introduce `S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => intro f hf`. Simplify using `using hf`.

Consider the case `insert σ S hσ ih`. Introduce `f hf`. Establish `h1` using `M.sub_mem (hst _ (ih f hf)) (M.smul_mem (a σ) (ih f hf))`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `y`.

Simplify using `only [Finset.prod_insert hσ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `set p : Fin n → O := fun τ => ∏ σ ∈ Finset.univ.erase τ, (a τ - a σ) with hp`. Use `⟨∏ τ, p τ, ?_, fun z => ?_⟩` and prove the remaining obligations. Use `Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun σ hσ => ?_` and prove the remaining obligations.

Conclude with `sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hσ) (ha h).symm`. Use `choose f hfM hf using fun τ => hsur τ (fun i => z (τ, i))`. Establish `h1` using `M.sum_mem (t := Finset.univ) fun τ _ => M.smul_mem (∏ σ ∈ Finset.univ.erase τ, p σ) (hprod (Finset.univ.erase τ) _ (hfM τ))`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `y`.

Take `⟨τ, i⟩` from `y`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single τ]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, hf]`. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), _root_.mul_assoc]`. Introduce `σ _ hσ`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Finset.prod_eq_zero (s := Finset.univ.erase σ) (i := τ) (f := fun ρ => a τ - a ρ) (Finset.mem_erase.2 ⟨hσ.symm, Finset.mem_univ _⟩) (sub_self _)]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
private theorem full_of_stable [IsDomain O] {n s : ℕ} (a : Fin n → O) (ha : Function.Injective a)
    (M : Submodule O (Fin n × Fin s → O))
    (hst : ∀ f ∈ M, (fun y : Fin n × Fin s => a y.1 * f y) ∈ M)
    (hsur : ∀ (τ : Fin n) (z : Fin s → O), ∃ f ∈ M, ∀ i, f (τ, i) = z i) :
    ∃ D : O, D ≠ 0 ∧ ∀ z, D • z ∈ M := by
  classical
  have hprod : ∀ (S : Finset (Fin n)), ∀ f ∈ M,
      (fun y : Fin n × Fin s => (∏ σ ∈ S, (a y.1 - a σ)) * f y) ∈ M := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro f hf; simpa using hf
    | insert σ S hσ ih =>
      intro f hf
      have h1 := M.sub_mem (hst _ (ih f hf)) (M.smul_mem (a σ) (ih f hf))
      convert h1 using 1
      funext y
      simp only [Finset.prod_insert hσ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  set p : Fin n → O := fun τ => ∏ σ ∈ Finset.univ.erase τ, (a τ - a σ) with hp
  refine ⟨∏ τ, p τ, ?_, fun z => ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun σ hσ => ?_
    exact sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hσ) (ha h).symm
  · choose f hfM hf using fun τ => hsur τ (fun i => z (τ, i))
    have h1 := M.sum_mem (t := Finset.univ) fun τ _ =>
      M.smul_mem (∏ σ ∈ Finset.univ.erase τ, p σ) (hprod (Finset.univ.erase τ) _ (hfM τ))
    convert h1 using 1
    funext y
    obtain ⟨τ, i⟩ := y
    rw [Finset.sum_apply, Finset.sum_eq_single τ]
    · simp only [Pi.smul_apply, smul_eq_mul, hf]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), _root_.mul_assoc]
    · intro σ _ hσ
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.prod_eq_zero (s := Finset.univ.erase σ) (i := τ) (f := fun ρ => a τ - a ρ)
        (Finset.mem_erase.2 ⟨hσ.symm, Finset.mem_univ _⟩) (sub_self _)]
      simp
    · simp

/- English proof (translation)
Take `⟨m, c, ⟨e⟩, rfl⟩` from `h`. Establish `hd : v (algebraMap O C (∏ i, c i)) = ∏ i, v (algebraMap O C (c i))`. Simplify using `only [map_prod]`. Use `⟨∏ i, c i, fun h0 => hx (by rw [← hd, h0]; simp), fun y => ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises.

Rewrite using `[map_smul, map_zero]`. Use function extensionality and compare the values at `i`. Take `⟨r, hr⟩` from `Ideal.Quotient.mk_surjective (e y i)`. Rewrite using `[Pi.smul_apply, ← hr, Pi.zero_apply, Algebra.smul_def]`. Use `show Ideal.Quotient.mk _ _ * _ = 0`.

Rewrite using `[← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Conclude with `(Finset.dvd_prod_of_mem c (Finset.mem_univ i)).mul_right r`.
-/
private theorem killed_of_hasLen {M : Type} [AddCommGroup M] [Module O M] {x : NNReal}
    (h : HasLen v O M x) (hx : x ≠ 0) : ∃ d : O, d ≠ 0 ∧ ∀ y : M, d • y = 0 := by
  obtain ⟨m, c, ⟨e⟩, rfl⟩ := h
  have hd : v (algebraMap O C (∏ i, c i)) = ∏ i, v (algebraMap O C (c i)) := by
    simp only [map_prod]
  refine ⟨∏ i, c i, fun h0 => hx (by rw [← hd, h0]; simp), fun y => ?_⟩
  apply e.injective
  rw [map_smul, map_zero]
  funext i
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e y i)
  rw [Pi.smul_apply, ← hr, Pi.zero_apply, Algebra.smul_def]
  show Ideal.Quotient.mk _ _ * _ = 0
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact (Finset.dvd_prod_of_mem c (Finset.mem_univ i)).mul_right r

omit [Algebra O C] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 hz`. Use `⟨∑ l, c l • φ l, Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(⟨0, τ.pos⟩, l), ?_⟩), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`.

Simplify using the standard rewrite rules. Use function extensionality and compare the values at `i`. Simplify using `[Finset.sum_apply]`. Introduce and unpack `⟨f, hf, rfl⟩`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 hf`.

Establish `h1` using `Submodule.sum_mem (Submodule.span O (Set.range fun l => fun i => φ l (τ, i))) (t := Finset.univ) (f := fun q : Fin n × Fin h => (c q * a τ ^ (q.1 : ℕ)) • fun i => φ q.2 (τ, i)) fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.2, rfl⟩)`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[Finset.sum_apply, _root_.mul_assoc]`.
-/
private theorem proj_span {n s h : ℕ} (a : Fin n → O) (φ : Fin h → Fin n × Fin s → O) (τ : Fin n)
    (z : Fin s → O) :
    z ∈ Submodule.span O (Set.range fun l => fun i => φ l (τ, i)) ↔
      ∃ f ∈ Submodule.span O (Set.range fun q : Fin n × Fin h =>
        fun y : Fin n × Fin s => a y.1 ^ (q.1 : ℕ) * φ q.2 y), z = fun i => f (τ, i) := by
  constructor
  · intro hz
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hz
    refine ⟨∑ l, c l • φ l, Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨(⟨0, τ.pos⟩, l), ?_⟩), ?_⟩
    · funext y; simp
    · funext i; simp [Finset.sum_apply]
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hf
    have h1 := Submodule.sum_mem (Submodule.span O (Set.range fun l => fun i => φ l (τ, i)))
      (t := Finset.univ) (f := fun q : Fin n × Fin h =>
        (c q * a τ ^ (q.1 : ℕ)) • fun i => φ q.2 (τ, i))
      fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.2, rfl⟩)
    convert h1 using 1
    funext i
    simp [Finset.sum_apply, _root_.mul_assoc]

end aux

/- English proof (translation)
Introduce `C _ _ v O _ _ hv hnt n s h a ha M hM hst hsur φ hφ c hc0 hc`. Establish `: IsDomain O` using `hv.hom_inj.isDomain`. Use `set M' := Submodule.span O (Set.range fun q : Fin n × Fin h => fun y : Fin n × Fin s => a y.1 ^ (q.1 : ℕ) * φ q.2 y) with hM'def`. Establish `hpow : ∀ (k : ℕ), ∀ f ∈ M, (fun y : Fin n × Fin s => a y.1 ^ k * f y) ∈ M`. Introduce `k f hf`.

Proceed by induction on `k with`. Consider the case `zero => simpa using hf`. Consider the case `succ k ih`. Use `hst _ ih using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `y`.

Expand and normalize the polynomial expressions, which then agree. Establish `hle : M' ≤ M` using `Submodule.span_le.2 (by rintro _ ⟨q, rfl⟩; exact hpow _ _ (hφ q.2))`. Take `⟨D, hD, hDM⟩` from `full_of_stable a ha M hst hsur`. Take `⟨d, hd, hdM⟩` from `killed_of_hasLen hc hc0`. Establish `hdD : d * D ≠ 0` using `mul_ne_zero hd hD`.

Establish `hDM' : ∀ z, (d * D) • z ∈ M'`. Introduce `z`. Establish `h1` using `hdM (Submodule.Quotient.mk ⟨D • z, hDM z⟩)`. Rewrite `h1` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[mul_smul]`.

Conclude with `h1`. Establish `hDτ : ∀ τ z, (d * D) • z ∈ Submodule.span O (Set.range fun l => fun i => φ l (τ, i))` using `fun τ z => (proj_span a φ τ _).2 ⟨_, hDM' (fun y => z y.2), rfl⟩`. Take `⟨B, hB, hBM⟩` from `exists_basisMat hv M hM D hD hDM`. Take `⟨B', hB', hBM'⟩` from `exists_basisMat hv M' (Submodule.fg_span (Set.finite_range _)) _ hdD hDM'`. Use `choose Bτ hBτ hBMτ using fun τ => exists_basisMat hv _ (Submodule.fg_span (Set.finite_range _)) _ hdD (hDτ τ)`.

Establish `hainj : Function.Injective fun τ => algebraMap O C (a τ)` using `hv.hom_inj.comp ha`. Set `L : Lat v (Fin n × Fin s)` to `⟨_, det_map_ne hv hB⟩`. Set `L' : Lat v (Fin n × Fin s)` to `⟨_, det_map_ne hv hB'⟩`. Set `Lτ : Fin n → Lat v (Fin s)` to `fun τ => ⟨_, det_map_ne hv (hBτ τ)⟩`. Set `F : Lat v (Fin n × Fin h)` to `⟨freeMat (fun τ => algebraMap O C (a τ)) h, by`.

Rewrite using `[det_freeMat]`. Conclude with `pow_ne_zero _ (Matrix.det_vandermonde_ne_zero_iff.2 hainj)⟩`. Establish `hL` using `mem_pts hv L rfl`. Establish `hL'` using `mem_pts hv L' rfl`. Establish `hLτ` using `fun τ => mem_pts hv (Lτ τ) rfl`.

Establish `hstd` using `mem_pts hv (B := 1) (Lat.std v (Fin s)) (by simp [Lat.std])`. Simplify using `only [hBM, hBM', hBMτ] at hL hL' hLτ`. Use `⟨fun τ => colen (Lτ τ) (Lat.std v (Fin s)), fun τ => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hasLen_coker_det' v O hv _ (Bτ τ)`. Rewrite `h1` using `[hBMτ, RingHom.map_det, RingHom.mapMatrix_apply]`.

Simplify `h1` using `[colen, Lat.std, Lτ]`. Use `lat_conseq C v O hv hnt n _ hainj (fun τ => hv.map_le_one _) s h (fun τ => Matrix.of fun i l => algebraMap O C (φ l (τ, i))) F L L' (fun _ => Lat.std v (Fin s)) Lτ rfl (fun τ => ?_) ?_ ?_ (fun τ => ?_) (fun τ => ?_) c (len_eq hv hB M M' hBM hBM' hle hc).le` and prove the remaining obligations. Introduce `w`. Establish `hne : algebraMap O C (d * D) ≠ 0` using `fun h0 => hdD (hv.hom_inj (by rw [h0, map_zero]))`. Use `choose r hr using fun j => (Submodule.mem_span_range_iff_exists_fun O).1 (hDτ τ (Pi.single j 1))`.

Use `⟨fun l => ∑ j, w j / algebraMap O C (d * D) * algebraMap O C (r j l), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `h1 : ∀ j, ∑ l, algebraMap O C (φ l (τ, i)) * algebraMap O C (r j l) = if i = j then algebraMap O C (d * D) else 0`. Introduce `j`. Establish `h2` using `congrArg (algebraMap O C) (congrFun (hr j) i)`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, Pi.single_apply, mul_ite, _root_.mul_one, mul_zero] at h2`. Rewrite `h2` using `[apply_ite (algebraMap O C), map_zero]`. Rewrite using `[← h2]`. Conclude with `Finset.sum_congr rfl fun l _ => by rw [map_mul, mul_comm]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Establish `h3 : ∀ j, ∑ l, algebraMap O C (φ l (τ, i)) * (w j / algebraMap O C (d * D) * algebraMap O C (r j l)) = if i = j then w j else 0`. Introduce `j`. Simplify using `only [mul_left_comm _ (w j / _), ← Finset.mul_sum, h1]`. Use `split_ifs`.

Conclude with `div_mul_cancel₀ _ hne`. Conclude with `mul_zero _`. Simplify using `only [h3]`. Simplify using the standard rewrite rules. Establish `key : ∀ c₀ : Fin n × Fin h → O, (fun y : Fin n × Fin s => ∑ l, algebraMap O C (φ l (y.1, y.2)) * (F.B *ᵥ fun q => algebraMap O C (c₀ q)) (y.1, l)) = fun j => algebraMap O C ((∑ q : Fin n × Fin h, c₀ q • fun y : Fin n × Fin s => a y.1 ^ (q.1 : ℕ) * φ q.2 y) j)`.

Introduce `c₀`. Use function extensionality and compare the values at `y`. Simplify using `only [F, freeMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_prod_type, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, map_pow, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.

Use extensionality with `x`. Rewrite using `[hL']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Take `⟨c₀, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun O).1 hz`.

Conclude with `⟨_, ⟨_, (integral_iff hv _).2 ⟨c₀, rfl⟩, rfl⟩, key c₀⟩`. Introduce and unpack `⟨_, ⟨c₁, hc₁, rfl⟩, rfl⟩`. Take `⟨c₀, rfl⟩` from `(integral_iff hv c₁).1 hc₁`. Conclude with `⟨_, (Submodule.mem_span_range_iff_exists_fun O).2 ⟨c₀, rfl⟩, key c₀⟩`. Introduce `w hw`.

Take `⟨z, hz, rfl⟩` from `(hL w).1 hw`. Conclude with `(hL _).2 ⟨_, hst z hz, by funext y; simp⟩`. Use extensionality with `x`. Rewrite using `[hstd]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, -, rfl⟩`. Take `⟨f, hf, hfz⟩` from `hsur τ z`. Conclude with `⟨_, (hL _).2 ⟨f, hf, rfl⟩, by funext i; simp [hfz]⟩`. Introduce and unpack `⟨w, hw, rfl⟩`. Take `⟨z, hz, rfl⟩` from `(hL w).1 hw`.

Conclude with `⟨fun i => z (τ, i), ⟨fun i => z (τ, i), by simp⟩, rfl⟩`. Use extensionality with `x`. Rewrite using `[hLτ]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`.

Take `⟨f, hf, rfl⟩` from `(proj_span a φ τ z).1 hz`. Conclude with `⟨_, (hL' _).2 ⟨f, hf, rfl⟩, rfl⟩`. Introduce and unpack `⟨w, hw, rfl⟩`. Take `⟨z, hz, rfl⟩` from `(hL' w).1 hw`. Conclude with `⟨fun i => z (τ, i), (proj_span a φ τ _).2 ⟨z, hz, rfl⟩, rfl⟩`.
-/
theorem lattice_ineq_integers : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → (∃ c : C, 0 < v c ∧ v c < 1) → ∀ (n s h : ℕ) (a : Fin n → O), Function.Injective a → ∀ (M : Submodule O (Fin n × Fin s → O)), M.FG → (∀ f ∈ M, (fun y : Fin n × Fin s => a y.1 * f y) ∈ M) → (∀ (τ : Fin n) (z : Fin s → O), ∃ f ∈ M, ∀ i, f (τ, i) = z i) → ∀ (φ : Fin h → Fin n × Fin s → O), (∀ l, φ l ∈ M) → ∀ c : NNReal, c ≠ 0 → HasLen v O (M ⧸ (Submodule.span O (Set.range fun q : Fin n × Fin h => fun y : Fin n × Fin s => a y.1 ^ (q.1 : ℕ) * φ q.2 y)).comap M.subtype) c → ∃ x : Fin n → NNReal, (∀ τ, HasLen v O ((Fin s → O) ⧸ Submodule.span O (Set.range fun l => fun i => φ l (τ, i))) (x τ)) ∧ c ^ 2 * v (discr fun τ => algebraMap O C (a τ)) ^ h ≤ (∏ τ, x τ) ^ 2 * v (discr fun τ => algebraMap O C (a τ)) ^ s := by
  intro C _ _ v O _ _ hv hnt n s h a ha M hM hst hsur φ hφ c hc0 hc
  have : IsDomain O := hv.hom_inj.isDomain
  set M' := Submodule.span O (Set.range fun q : Fin n × Fin h =>
    fun y : Fin n × Fin s => a y.1 ^ (q.1 : ℕ) * φ q.2 y) with hM'def
  have hpow : ∀ (k : ℕ), ∀ f ∈ M, (fun y : Fin n × Fin s => a y.1 ^ k * f y) ∈ M := by
    intro k f hf
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      convert hst _ ih using 1
      funext y
      ring
  have hle : M' ≤ M := Submodule.span_le.2 (by rintro _ ⟨q, rfl⟩; exact hpow _ _ (hφ q.2))
  obtain ⟨D, hD, hDM⟩ := full_of_stable a ha M hst hsur
  obtain ⟨d, hd, hdM⟩ := killed_of_hasLen hc hc0
  have hdD : d * D ≠ 0 := mul_ne_zero hd hD
  have hDM' : ∀ z, (d * D) • z ∈ M' := by
    intro z
    have h1 := hdM (Submodule.Quotient.mk ⟨D • z, hDM z⟩)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
    rw [mul_smul]
    exact h1
  have hDτ : ∀ τ z, (d * D) • z ∈ Submodule.span O (Set.range fun l => fun i => φ l (τ, i)) :=
    fun τ z => (proj_span a φ τ _).2 ⟨_, hDM' (fun y => z y.2), rfl⟩
  obtain ⟨B, hB, hBM⟩ := exists_basisMat hv M hM D hD hDM
  obtain ⟨B', hB', hBM'⟩ := exists_basisMat hv M' (Submodule.fg_span (Set.finite_range _)) _ hdD hDM'
  choose Bτ hBτ hBMτ using fun τ => exists_basisMat hv _
    (Submodule.fg_span (Set.finite_range _)) _ hdD (hDτ τ)
  have hainj : Function.Injective fun τ => algebraMap O C (a τ) := hv.hom_inj.comp ha
  let L : Lat v (Fin n × Fin s) := ⟨_, det_map_ne hv hB⟩
  let L' : Lat v (Fin n × Fin s) := ⟨_, det_map_ne hv hB'⟩
  let Lτ : Fin n → Lat v (Fin s) := fun τ => ⟨_, det_map_ne hv (hBτ τ)⟩
  let F : Lat v (Fin n × Fin h) := ⟨freeMat (fun τ => algebraMap O C (a τ)) h, by
    rw [det_freeMat]
    exact pow_ne_zero _ (Matrix.det_vandermonde_ne_zero_iff.2 hainj)⟩
  have hL := mem_pts hv L rfl
  have hL' := mem_pts hv L' rfl
  have hLτ := fun τ => mem_pts hv (Lτ τ) rfl
  have hstd := mem_pts hv (B := 1) (Lat.std v (Fin s)) (by simp [Lat.std])
  simp only [hBM, hBM', hBMτ] at hL hL' hLτ
  refine ⟨fun τ => colen (Lτ τ) (Lat.std v (Fin s)), fun τ => ?_, ?_⟩
  · have h1 := hasLen_coker_det' v O hv _ (Bτ τ)
    rw [hBMτ, RingHom.map_det, RingHom.mapMatrix_apply] at h1
    simpa [colen, Lat.std, Lτ] using h1
  refine lat_conseq C v O hv hnt n _ hainj (fun τ => hv.map_le_one _) s h
    (fun τ => Matrix.of fun i l => algebraMap O C (φ l (τ, i))) F L L' (fun _ => Lat.std v (Fin s))
    Lτ rfl (fun τ => ?_) ?_ ?_ (fun τ => ?_) (fun τ => ?_) c (len_eq hv hB M M' hBM hBM' hle hc).le
  · intro w
    have hne : algebraMap O C (d * D) ≠ 0 := fun h0 => hdD (hv.hom_inj (by rw [h0, map_zero]))
    choose r hr using fun j => (Submodule.mem_span_range_iff_exists_fun O).1
      (hDτ τ (Pi.single j 1))
    refine ⟨fun l => ∑ j, w j / algebraMap O C (d * D) * algebraMap O C (r j l), ?_⟩
    funext i
    have h1 : ∀ j, ∑ l, algebraMap O C (φ l (τ, i)) * algebraMap O C (r j l) =
        if i = j then algebraMap O C (d * D) else 0 := by
      intro j
      have h2 := congrArg (algebraMap O C) (congrFun (hr j) i)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, Pi.single_apply, mul_ite,
        _root_.mul_one, mul_zero] at h2
      rw [apply_ite (algebraMap O C), map_zero] at h2
      rw [← h2]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul, mul_comm]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h3 : ∀ j, ∑ l, algebraMap O C (φ l (τ, i)) *
        (w j / algebraMap O C (d * D) * algebraMap O C (r j l)) =
        if i = j then w j else 0 := by
      intro j
      simp only [mul_left_comm _ (w j / _), ← Finset.mul_sum, h1]
      split_ifs
      · exact div_mul_cancel₀ _ hne
      · exact mul_zero _
    simp only [h3]
    simp
  · have key : ∀ c₀ : Fin n × Fin h → O, (fun y : Fin n × Fin s =>
        ∑ l, algebraMap O C (φ l (y.1, y.2)) *
          (F.B *ᵥ fun q => algebraMap O C (c₀ q)) (y.1, l)) =
        fun j => algebraMap O C ((∑ q : Fin n × Fin h, c₀ q •
          fun y : Fin n × Fin s => a y.1 ^ (q.1 : ℕ) * φ q.2 y) j) := by
      intro c₀
      funext y
      simp only [F, freeMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_prod_type,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, map_pow, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    ext x
    rw [hL']
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨c₀, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hz
      exact ⟨_, ⟨_, (integral_iff hv _).2 ⟨c₀, rfl⟩, rfl⟩, key c₀⟩
    · rintro ⟨_, ⟨c₁, hc₁, rfl⟩, rfl⟩
      obtain ⟨c₀, rfl⟩ := (integral_iff hv c₁).1 hc₁
      exact ⟨_, (Submodule.mem_span_range_iff_exists_fun O).2 ⟨c₀, rfl⟩, key c₀⟩
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := (hL w).1 hw
    exact (hL _).2 ⟨_, hst z hz, by funext y; simp⟩
  · ext x
    rw [hstd]
    constructor
    · rintro ⟨z, -, rfl⟩
      obtain ⟨f, hf, hfz⟩ := hsur τ z
      exact ⟨_, (hL _).2 ⟨f, hf, rfl⟩, by funext i; simp [hfz]⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨z, hz, rfl⟩ := (hL w).1 hw
      exact ⟨fun i => z (τ, i), ⟨fun i => z (τ, i), by simp⟩, rfl⟩
  · ext x
    rw [hLτ]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨f, hf, rfl⟩ := (proj_span a φ τ z).1 hz
      exact ⟨_, (hL' _).2 ⟨f, hf, rfl⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨z, hz, rfl⟩ := (hL' w).1 hw
      exact ⟨fun i => z (τ, i), (proj_span a φ τ _).2 ⟨z, hz, rfl⟩, rfl⟩

end GlobalTheory.ChF
