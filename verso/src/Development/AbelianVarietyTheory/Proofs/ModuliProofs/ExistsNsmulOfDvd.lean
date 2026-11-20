import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.HeckeKerZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckeKerAll

open GlobalTheory.HeckeTate GlobalTheory.HeckeKerModel

/- English proof (translation)
Establish `: Fintype Y` using `Fintype.ofFinite Y`. Establish `hinj : Function.Injective (fun φ : Y →+ ZMod m => (ZMod.stdAddChar (N` using `m)).compAddMonoidHom φ) := by`. Introduce `φ ψ h`. Use extensionality with `y`. Conclude with `ZMod.injective_stdAddChar (DFunLike.congr_fun h y)`.

Establish `: Finite (Y →+ ZMod m)` using `Finite.of_injective _ hinj`. Rewrite using `[AddSubgroup.index_ker]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem index_ker_le_card {X Y : Type} [AddCommGroup X] [AddCommGroup Y] [Finite Y] {m : ℕ} [NeZero m]
    (F : X →+ (Y →+ ZMod m)) : F.ker.index ≤ Nat.card Y := by
  classical
  have : Fintype Y := Fintype.ofFinite Y
  have hinj : Function.Injective
      (fun φ : Y →+ ZMod m => (ZMod.stdAddChar (N := m)).compAddMonoidHom φ) := by
    intro φ ψ h
    ext y
    exact ZMod.injective_stdAddChar (DFunLike.congr_fun h y)
  have : Finite (Y →+ ZMod m) := Finite.of_injective _ hinj
  rw [AddSubgroup.index_ker]
  calc Nat.card F.range ≤ Nat.card (Y →+ ZMod m) := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ ≤ Nat.card (AddChar Y ℂ) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card Y := by simp only [Nat.card_eq_fintype_card, AddChar.card_eq]

/- English proof (translation)
Use `choose q hq using h1`. Establish `hm' : (m : ℤ) ≠ 0` using `by exact_mod_cast hm`. Establish `hadd : ∀ y z, q (y + z) = q y + q z`. Introduce `y z`. Apply `mul_left_cancel₀ hm'` to reduce the goal to its premises.

Rewrite using `[mul_add, ← hq, ← hq, ← hq, map_add]`. Take `⟨z, hz⟩` from `hB.2 (AddMonoidHom.mk' q hadd)`. Use `⟨z, hB.1 ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Simplify using `[hz, hq]`.
-/
theorem exists_nsmul_of_dvd {M : Type} [AddCommGroup M] (B : M →+ M →+ ℤ) (hB : Function.Bijective B) {m : ℕ}
    (hm : m ≠ 0) {x : M} (h1 : ∀ y, (m : ℤ) ∣ B x y) : ∃ z, m • z = x := by
  choose q hq using h1
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm
  have hadd : ∀ y z, q (y + z) = q y + q z := by
    intro y z
    apply mul_left_cancel₀ hm'
    rw [mul_add, ← hq, ← hq, ← hq, map_add]
  obtain ⟨z, hz⟩ := hB.2 (AddMonoidHom.mk' q hadd)
  refine ⟨z, hB.1 ?_⟩
  ext y
  simp [hz, hq]

/- English proof (translation)
Establish `: NeZero m` using `⟨hm⟩`. Use `set K := (nsmulAddMonoidHom (α := M) m).range with hK_eq`. Establish `hK : K.index = m ^ Module.finrank ℤ M` using `AddSubgroup.index_range_nsmul M m`. Establish `hN : m ^ Module.finrank ℤ M ≠ 0` using `pow_ne_zero _ hm`. Establish `hKD : K ≤ D`.

Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[hD]`. Introduce `y _`. Simplify using `[map_nsmul]`. Establish `e1` using `AddSubgroup.relIndex_mul_index hC`.

Establish `e2` using `AddSubgroup.relIndex_mul_index hKD`. Rewrite `e1`, `e2` using `[hK]`. Establish `hC0 : C.index ≠ 0` using `fun h => hN (by rw [← e1, h, mul_zero])`. Establish `hKC0 : K.relIndex C ≠ 0` using `fun h => hN (by rw [← e1, h, zero_mul])`. Establish `i1 : D.index ≤ K.relIndex C`.

Establish `: (K.addSubgroupOf C).FiniteIndex` using `⟨hKC0⟩`. Set `g : M → (C →+ ZMod m)` to `fun x => (Int.castAddHom (ZMod m)).comp ((B x).comp C.subtype)`. Establish `hg : ∀ x, K.addSubgroupOf C ≤ (g x).ker`. Introduce and unpack `x ⟨c, hc⟩ hcK`. Rewrite `hcK` using `[AddSubgroup.mem_addSubgroupOf]`.

Take `⟨w, hw⟩` from `hcK`. Establish `hw' : m • w = c` using `hw`. Rewrite using `[AddMonoidHom.mem_ker]`. Simplify using `only [g, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, Int.coe_castAddHom]`. Rewrite using `[← hw']`.

Simplify using `[map_nsmul]`. Set `F1 : M →+ (C ⧸ K.addSubgroupOf C →+ ZMod m)` to `AddMonoidHom.mk' (fun x => QuotientAddGroup.lift _ (g x) (hg x)) (by`. Introduce `x y`. Use `AddMonoidHom.ext fun q => QuotientAddGroup.induction_on q fun c => ?_` and prove the remaining obligations. Simplify using `[g])`.

Establish `hk : F1.ker = D`. Use extensionality with `x`. Rewrite using `[AddMonoidHom.mem_ker, hD]`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`.

Use `DFunLike.congr_fun h ((⟨y, hy⟩ : C) : C ⧸ K.addSubgroupOf C)` as an intermediate fact. Simplify `this` using `[F1, g, ZMod.intCast_zmod_eq_zero_iff_dvd]`. Introduce `h`. Use `AddMonoidHom.ext fun q => QuotientAddGroup.induction_on q fun c => ?_` and prove the remaining obligations. Simplify `h c c.2` using `[F1, g, ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Rewrite using `[← hk]`. Combine the equalities or inequalities in the displayed calculation. Establish `i2 : K.relIndex D ≤ C.index`. Establish `: C.FiniteIndex` using `⟨hC0⟩`. Set `g : D → (M →+ ZMod m)` to `fun d => (Int.castAddHom (ZMod m)).comp (B d)`.

Establish `hg : ∀ d : D, C ≤ (g d).ker`. Introduce `d y hy`. Rewrite using `[AddMonoidHom.mem_ker]`. Simplify `(hD d).1 d.2 y hy` using `[g, ZMod.intCast_zmod_eq_zero_iff_dvd]`. Set `F2 : D →+ (M ⧸ C →+ ZMod m)` to `AddMonoidHom.mk' (fun d => QuotientAddGroup.lift C (g d) (hg d)) (by`.

Introduce `d e`. Use `AddMonoidHom.ext fun q => QuotientAddGroup.induction_on q fun y => ?_` and prove the remaining obligations. Simplify using `[g])`. Establish `hk : F2.ker = K.addSubgroupOf D`. Use extensionality with `d`.

Rewrite using `[AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨z, hz⟩` from `exists_nsmul_of_dvd B hB hm (x := (d : M)) fun y => by`. Use `DFunLike.congr_fun h (y : M ⧸ C)` as an intermediate fact.

Simplify `this` using `[F2, g, ZMod.intCast_zmod_eq_zero_iff_dvd]`. Conclude with `⟨z, hz⟩`. Introduce and unpack `⟨w, hw⟩`. Use `AddMonoidHom.ext fun q => QuotientAddGroup.induction_on q fun y => ?_` and prove the remaining obligations. Simplify using `only [F2, g, AddMonoidHom.mk'_apply, QuotientAddGroup.lift_mk, AddMonoidHom.comp_apply, Int.coe_castAddHom, AddMonoidHom.zero_apply]`.

Rewrite using `[← hw]`. Simplify using `[map_nsmul]`. Combine the equalities or inequalities in the displayed calculation. Apply `le_antisymm` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem relIndex_orth {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (B : M →+ M →+ ℤ)
    (hB : Function.Bijective B) {m : ℕ} (hm : m ≠ 0) (C D : AddSubgroup M)
    (hC : (nsmulAddMonoidHom (α := M) m).range ≤ C) (hD : ∀ x, x ∈ D ↔ ∀ y ∈ C, (m : ℤ) ∣ B x y) :
    (nsmulAddMonoidHom (α := M) m).range.relIndex C * (nsmulAddMonoidHom (α := M) m).range.relIndex D =
      m ^ Module.finrank ℤ M := by
  classical
  have : NeZero m := ⟨hm⟩
  set K := (nsmulAddMonoidHom (α := M) m).range with hK_eq
  have hK : K.index = m ^ Module.finrank ℤ M := AddSubgroup.index_range_nsmul M m
  have hN : m ^ Module.finrank ℤ M ≠ 0 := pow_ne_zero _ hm
  have hKD : K ≤ D := by
    rintro _ ⟨w, rfl⟩
    rw [hD]
    intro y _
    simp [map_nsmul]
  have e1 := AddSubgroup.relIndex_mul_index hC
  have e2 := AddSubgroup.relIndex_mul_index hKD
  rw [hK] at e1 e2
  have hC0 : C.index ≠ 0 := fun h => hN (by rw [← e1, h, mul_zero])
  have hKC0 : K.relIndex C ≠ 0 := fun h => hN (by rw [← e1, h, zero_mul])
  have i1 : D.index ≤ K.relIndex C := by
    have : (K.addSubgroupOf C).FiniteIndex := ⟨hKC0⟩
    let g : M → (C →+ ZMod m) := fun x => (Int.castAddHom (ZMod m)).comp ((B x).comp C.subtype)
    have hg : ∀ x, K.addSubgroupOf C ≤ (g x).ker := by
      rintro x ⟨c, hc⟩ hcK
      rw [AddSubgroup.mem_addSubgroupOf] at hcK
      obtain ⟨w, hw⟩ := hcK
      have hw' : m • w = c := hw
      rw [AddMonoidHom.mem_ker]
      simp only [g, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, Int.coe_castAddHom]
      rw [← hw']
      simp [map_nsmul]
    let F1 : M →+ (C ⧸ K.addSubgroupOf C →+ ZMod m) :=
      AddMonoidHom.mk' (fun x => QuotientAddGroup.lift _ (g x) (hg x)) (by
        intro x y
        refine AddMonoidHom.ext fun q => QuotientAddGroup.induction_on q fun c => ?_
        simp [g])
    have hk : F1.ker = D := by
      ext x
      rw [AddMonoidHom.mem_ker, hD]
      constructor
      · intro h y hy
        have := DFunLike.congr_fun h ((⟨y, hy⟩ : C) : C ⧸ K.addSubgroupOf C)
        simpa [F1, g, ZMod.intCast_zmod_eq_zero_iff_dvd] using this
      · intro h
        refine AddMonoidHom.ext fun q => QuotientAddGroup.induction_on q fun c => ?_
        simpa [F1, g, ZMod.intCast_zmod_eq_zero_iff_dvd] using h c c.2
    rw [← hk]
    calc F1.ker.index ≤ Nat.card (C ⧸ K.addSubgroupOf C) := index_ker_le_card F1
      _ = K.relIndex C := by rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card]
  have i2 : K.relIndex D ≤ C.index := by
    have : C.FiniteIndex := ⟨hC0⟩
    let g : D → (M →+ ZMod m) := fun d => (Int.castAddHom (ZMod m)).comp (B d)
    have hg : ∀ d : D, C ≤ (g d).ker := by
      intro d y hy
      rw [AddMonoidHom.mem_ker]
      simpa [g, ZMod.intCast_zmod_eq_zero_iff_dvd] using (hD d).1 d.2 y hy
    let F2 : D →+ (M ⧸ C →+ ZMod m) :=
      AddMonoidHom.mk' (fun d => QuotientAddGroup.lift C (g d) (hg d)) (by
        intro d e
        refine AddMonoidHom.ext fun q => QuotientAddGroup.induction_on q fun y => ?_
        simp [g])
    have hk : F2.ker = K.addSubgroupOf D := by
      ext d
      rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
      constructor
      · intro h
        obtain ⟨z, hz⟩ := exists_nsmul_of_dvd B hB hm (x := (d : M)) fun y => by
          have := DFunLike.congr_fun h (y : M ⧸ C)
          simpa [F2, g, ZMod.intCast_zmod_eq_zero_iff_dvd] using this
        exact ⟨z, hz⟩
      · rintro ⟨w, hw⟩
        refine AddMonoidHom.ext fun q => QuotientAddGroup.induction_on q fun y => ?_
        simp only [F2, g, AddMonoidHom.mk'_apply, QuotientAddGroup.lift_mk, AddMonoidHom.comp_apply,
          Int.coe_castAddHom, AddMonoidHom.zero_apply]
        rw [← hw]
        simp [map_nsmul]
    calc K.relIndex D = F2.ker.index := by rw [hk]; rfl
      _ ≤ Nat.card (M ⧸ C) := index_ker_le_card F2
      _ = C.index := (AddSubgroup.index_eq_card _).symm
  apply le_antisymm
  · calc K.relIndex C * K.relIndex D ≤ K.relIndex C * C.index := Nat.mul_le_mul_left _ i2
      _ = _ := e1
  · calc m ^ Module.finrank ℤ M = K.relIndex D * D.index := e2.symm
      _ ≤ K.relIndex D * K.relIndex C := Nat.mul_le_mul_left _ i1
      _ = _ := Nat.mul_comm _ _

/- English proof (translation)
Establish `: P.IsPrime` using `hP.isPrime`. Take `⟨φ, φ', s, hs, -, h2⟩` from `GlobalTheory.HeckeTate.exists_local_iso (R := R) (M := M) (M' := Fin (Module.finrank R M) → R) (by simp) P`. Take `⟨u, e, he, hue⟩` from `hP.exists_inv hs`. Set `gL : M →ₗ[R] (Fin i → R ⧸ P)` to `{ toFun := fun x j => Ideal.Quotient.mk P (φ x (Fin.castLE hi j)) map_add' := by`. Introduce `x y`.

Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Use the proof step `map_smul' := by`. Introduce `c x`. Use function extensionality and compare the values at `j`.

Simplify using `only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]`. Use `rfl }`. Establish `hsurj : Function.Surjective gL`. Introduce `t`. Use `choose y0 hy0 using fun j => Ideal.Quotient.mk_surjective (I := P) (t j)`.

Set `y : Fin (Module.finrank R M) → R` to `fun k => if h : (k : ℕ) < i then y0 ⟨k, h⟩ else 0`. Use `⟨u • φ' y, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk P (φ (u • φ' y) (Fin.castLE hi j)) = t j`. Rewrite using `[map_smul, h2, smul_smul, Pi.smul_apply, smul_eq_mul]`.

Establish `hyj : y (Fin.castLE hi j) = y0 j`. Simplify using `[y, j.2]`. Rewrite using `[hyj, ← hy0 j, Ideal.Quotient.eq]`. Establish `: u * s * y0 j - y0 j = -(e * y0 j)`. Take the linear combination `(y0 j) * hue`.

Rewrite using `[this]`. Conclude with `P.neg_mem (P.mul_mem_right _ he)`. Use `⟨LinearMap.ker gL, ?_, ?_⟩` and prove the remaining obligations. Introduce `c hc x`. Rewrite using `[LinearMap.mem_ker]`.

Use function extensionality and compare the values at `j`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk P (φ (c • x) (Fin.castLE hi j)) = 0`. Rewrite using `[map_smul, Pi.smul_apply, smul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `P.mul_mem_right _ hc`. Establish `hk : (LinearMap.ker gL).toAddSubgroup = (gL.toAddMonoidHom).ker` using `rfl`.

Rewrite using `[hk, AddSubgroup.index_eq_card, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv]`. Simplify using `[Nat.card_fun]`.
-/
theorem exists_sublattice {R : Type} [CommRing R] [IsDedekindDomain R] {M : Type} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] (P : Ideal R) (hP : P.IsMaximal) {i : ℕ}
    (hi : i ≤ Module.finrank R M) :
    ∃ L : Submodule R M, (∀ a ∈ P, ∀ x, a • x ∈ L) ∧ L.toAddSubgroup.index = Nat.card (R ⧸ P) ^ i := by
  classical
  have : P.IsPrime := hP.isPrime
  obtain ⟨φ, φ', s, hs, -, h2⟩ := GlobalTheory.HeckeTate.exists_local_iso (R := R) (M := M)
    (M' := Fin (Module.finrank R M) → R) (by simp) P
  obtain ⟨u, e, he, hue⟩ := hP.exists_inv hs
  let gL : M →ₗ[R] (Fin i → R ⧸ P) :=
    { toFun := fun x j => Ideal.Quotient.mk P (φ x (Fin.castLE hi j))
      map_add' := by
        intro x y
        funext j
        simp
      map_smul' := by
        intro c x
        funext j
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rfl }
  have hsurj : Function.Surjective gL := by
    intro t
    choose y0 hy0 using fun j => Ideal.Quotient.mk_surjective (I := P) (t j)
    let y : Fin (Module.finrank R M) → R := fun k => if h : (k : ℕ) < i then y0 ⟨k, h⟩ else 0
    refine ⟨u • φ' y, ?_⟩
    funext j
    change Ideal.Quotient.mk P (φ (u • φ' y) (Fin.castLE hi j)) = t j
    rw [map_smul, h2, smul_smul, Pi.smul_apply, smul_eq_mul]
    have hyj : y (Fin.castLE hi j) = y0 j := by
      simp [y, j.2]
    rw [hyj, ← hy0 j, Ideal.Quotient.eq]
    have : u * s * y0 j - y0 j = -(e * y0 j) := by
      linear_combination (y0 j) * hue
    rw [this]
    exact P.neg_mem (P.mul_mem_right _ he)
  refine ⟨LinearMap.ker gL, ?_, ?_⟩
  · intro c hc x
    rw [LinearMap.mem_ker]
    funext j
    change Ideal.Quotient.mk P (φ (c • x) (Fin.castLE hi j)) = 0
    rw [map_smul, Pi.smul_apply, smul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact P.mul_mem_right _ hc
  · have hk : (LinearMap.ker gL).toAddSubgroup = (gL.toAddMonoidHom).ker := rfl
    rw [hk, AddSubgroup.index_eq_card,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv]
    simp [Nat.card_fun]

/- English proof (translation)
Unfold `IsUnimod at h`. Take `⟨halt, hsesq, hbij⟩` from `h`. Establish `hp' : (p : ℤ) ≠ 0` using `by exact_mod_cast hp`. Establish `hBn : ∀ (k : ℕ) (u y : M), B (k • u) y = k * B u y` using `by intro k u y; simp [map_nsmul]`. Establish `hBn2 : ∀ (k : ℕ) (u y : M), B u (k • y) = k * B u y` using `by intro k u y; simp [map_nsmul]`.

Establish `hcan : ∀ u v : M, p • u = p • v → u = v`. Introduce `u v huv`. Apply `hbij.1` to reduce the goal to its premises. Use extensionality with `y`. Apply `mul_left_cancel₀ hp'` to reduce the goal to its premises.

Rewrite using `[← hBn, ← hBn, huv]`. Establish `hpL : ∀ z, p • z ∈ L` using `fun z => by`. Rewrite using `[← Nat.cast_smul_eq_nsmul R]`. Conclude with `hL _ hpP z`. Set `X : Submodule R M` to `{ carrier := {x | ∀ z ∈ L, (p : ℤ) ∣ B x z} add_mem' := by`.

Introduce `x y hx hy`. Simplify using `only [Set.mem_ofPred_eq] at *`. Introduce `z hz`. Simplify using `using dvd_add (hx z hz) (hy z hz)`. Use the proof step `zero_mem' := by`.

Simplify using `only [Set.mem_ofPred_eq]`. Introduce `z _`. Simplify using the standard rewrite rules. Use the proof step `smul_mem' := by`. Introduce `c x hx`.

Simplify using `only [Set.mem_ofPred_eq] at *`. Introduce `z hz`. Rewrite using `[hsesq]`. Conclude with `hx _ (L.smul_mem _ hz) }`. Establish `hX : ∀ x, x ∈ X ↔ ∀ z ∈ L, (p : ℤ) ∣ B x z` using `fun x => Iff.rfl`.

Establish `kX : ∀ c ∈ P, ∀ x ∈ X, ∃ w, σ c • x = p • w`. Introduce `c hc x hx`. Take `⟨w, hw⟩` from `exists_nsmul_of_dvd B hbij hp (x := σ c • x) fun y => by`. Rewrite using `[hsesq, hσ]`. Conclude with `(hX x).1 hx _ (hL c hc y)`.

Conclude with `⟨w, hw.symm⟩`. Set `N : Submodule R M` to `{ carrier := {y | ∃ l ∈ L, ∃ x ∈ X, y = p • l + a • x} add_mem' := by`. Introduce and unpack `_ _ ⟨l1, hl1, x1, hx1, rfl⟩ ⟨l2, hl2, x2, hx2, rfl⟩`. Conclude with `⟨l1 + l2, L.add_mem hl1 hl2, x1 + x2, X.add_mem hx1 hx2, by rw [smul_add, smul_add]; abel⟩`. Use the proof step `zero_mem' := ⟨0, L.zero_mem, 0, X.zero_mem, by simp⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c _ ⟨l, hl, x, hx, rfl⟩`. Conclude with `⟨c • l, L.smul_mem c hl, c • x, X.smul_mem c hx, by`. Rewrite using `[smul_add, smul_comm c p l, smul_comm c a x]⟩ }`. Establish `hN : ∀ y, y ∈ N ↔ ∃ l ∈ L, ∃ x ∈ X, y = p • l + a • x` using `fun y => Iff.rfl`.

Establish `h1 : ∀ z, p • z ∈ N ↔ z ∈ L`. Introduce `z`. Rewrite using `[hN]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨l, hl, x, hx, e⟩`.

Take `⟨w', hw'⟩` from `kX b hb x hx`. Establish `hw : p • (z - l) = a • x` using `by rw [smul_sub, e]; abel`. Establish `hs : σ b • (z - l) = a • w'`. Apply `hcan` to reduce the goal to its premises. Rewrite using `[smul_comm p (σ b) (z - l), hw, smul_comm (σ b) a x, hw', smul_comm a p w']`.

Establish `hzl : z - l ∈ L`. Establish `e2 : z - l = a • (z - l) + σ b • (z - l)` using `by rw [← add_smul, hab, one_smul]`. Rewrite using `[e2, hs]`. Conclude with `L.add_mem (hL a ha _) (hL a ha _)`. Simplify using `using L.add_mem hzl hl`.

Introduce `hz`. Conclude with `⟨z, hz, 0, X.zero_mem, by simp⟩`. Establish `h2 : ∀ c ∈ P, ∀ x ∈ N, ∃ z, σ c • x = p • z`. Introduce `c hc y hy`. Take `⟨l, hl, x, hx, rfl⟩` from `(hN y).1 hy`.

Take `⟨w, hw⟩` from `kX c hc x hx`. Conclude with `⟨σ c • l + a • w, by`. Rewrite using `[smul_add, smul_add, smul_comm (σ c) p l, smul_comm (σ c) a x, hw, smul_comm a p w]⟩`. Establish `h3 : ∀ x ∈ N, ∀ y ∈ N, ((p * p : ℕ) : ℤ) ∣ B x y`. Introduce `x hx y hy`.

Take `⟨l1, hl1, x1, hx1, rfl⟩` from `(hN x).1 hx`. Take `⟨l2, hl2, x2, hx2, rfl⟩` from `(hN y).1 hy`. Take `⟨w, hw⟩` from `kX a ha x2 hx2`. Take `⟨k1, hk1⟩ : (p : ℤ) ∣ B (a • x2) l1` from `(hX _).1 (X.smul_mem a hx2) l1 hl1`. Take `⟨k2, hk2⟩ : (p : ℤ) ∣ B (a • x1) l2` from `(hX _).1 (X.smul_mem a hx1) l2 hl2`.

Take `⟨k3, hk3⟩ : (p : ℤ) ∣ B x1 (a • w)` from `(hX _).1 hx1 _ (hL a ha w)`. Establish `e4 : B (a • x1) (a • x2) = p * B x1 (a • w)`. Rewrite using `[hsesq, smul_comm (σ a) a x2, hw, smul_comm a p w, hBn2]`. Establish `e2 : B l1 (a • x2) = - B (a • x2) l1` using `by rw [halt]`. Use `⟨B l1 l2 - k1 + k2 + k3, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, AddMonoidHom.add_apply, hBn, hBn2, e4, e2, hk1, hk2, hk3]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hdd : ∀ l : M, (∀ y ∈ X, (p : ℤ) ∣ B l y) → l ∈ L`. Establish `hKL : (nsmulAddMonoidHom (α` using `M) p).range ≤ L.toAddSubgroup := by`.

Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `hpL w`. Establish `hKX : (nsmulAddMonoidHom (α` using `M) p).range ≤ X.toAddSubgroup := by`. Introduce and unpack `_ ⟨w, rfl⟩`. Use `show p • w ∈ X`.

Rewrite using `[hX]`. Introduce `z _`. Rewrite using `[hBn]`. Conclude with `dvd_mul_right _ _`. Set `L2 : AddSubgroup M` to `{ carrier := {l | ∀ y ∈ X, (p : ℤ) ∣ B l y} add_mem' := by`.

Introduce `u v hu hv`. Simplify using `only [Set.mem_ofPred_eq] at *`. Introduce `y hy`. Simplify using `using dvd_add (hu y hy) (hv y hy)`. Use the proof step `zero_mem' := by`.

Simplify using `only [Set.mem_ofPred_eq]`. Introduce `y _`. Simplify using the standard rewrite rules. Use the proof step `neg_mem' := by`. Introduce `u hu`.

Simplify using `only [Set.mem_ofPred_eq] at *`. Introduce `y hy`. Simplify using `using (hu y hy).neg_right }`. Establish `o1 : (nsmulAddMonoidHom (α` using `M) p).range.relIndex L.toAddSubgroup * (nsmulAddMonoidHom (α := M) p).range.relIndex X.toAddSubgroup = p ^ Module.finrank ℤ M := relIndex_orth B hbij hp L.toAddSubgroup X.toAddSubgroup hKL (fun x => hX x)`. Establish `o2 : (nsmulAddMonoidHom (α` using `M) p).range.relIndex X.toAddSubgroup * (nsmulAddMonoidHom (α := M) p).range.relIndex L2 = p ^ Module.finrank ℤ M := relIndex_orth B hbij hp X.toAddSubgroup L2 hKX (fun x => Iff.rfl)`.

Establish `hLL2 : L.toAddSubgroup ≤ L2`. Introduce `l hl`. Use `show ∀ y ∈ X, (p : ℤ) ∣ B l y`. Introduce `y hy`. Rewrite using `[halt]`.

Conclude with `((hX y).1 hy l hl).neg_right`. Establish `o3` using `AddSubgroup.relIndex_mul_relIndex _ _ _ hKL hLL2`. Establish `hX0 : (nsmulAddMonoidHom (α` using `M) p).range.relIndex X.toAddSubgroup ≠ 0 := by`. Introduce `h0`. Rewrite `o2` using `[h0, zero_mul]`.

Conclude with `pow_ne_zero _ hp o2.symm`. Establish `hL0 : (nsmulAddMonoidHom (α` using `M) p).range.relIndex L.toAddSubgroup ≠ 0 := by`. Introduce `h0`. Rewrite `o1` using `[h0, zero_mul]`. Conclude with `pow_ne_zero _ hp o1.symm`.

Establish `eq12 : (nsmulAddMonoidHom (α` using `M) p).range.relIndex L.toAddSubgroup = (nsmulAddMonoidHom (α := M) p).range.relIndex L2 := by`. Apply `mul_right_cancel₀ hX0` to reduce the goal to its premises. Rewrite using `[o1, mul_comm, o2]`. Establish `hone : L.toAddSubgroup.relIndex L2 = 1`. Apply `mul_left_cancel₀ hL0` to reduce the goal to its premises.

Rewrite using `[o3, Nat.mul_one, eq12]`. Introduce `l hl`. Conclude with `AddSubgroup.relIndex_eq_one.1 hone hl`. Establish `hKN : (nsmulAddMonoidHom (α` using `M) (p * p)).range ≤ N.toAddSubgroup := by`. Introduce and unpack `_ ⟨w, rfl⟩`.

Use `show (p * p) • w ∈ N`. Rewrite using `[mul_smul]`. Conclude with `(h1 _).2 (hpL w)`. Establish `hself : ∀ x, x ∈ N.toAddSubgroup ↔ ∀ y ∈ N.toAddSubgroup, ((p * p : ℕ) : ℤ) ∣ B x y`. Introduce `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx y hy`. Conclude with `h3 x hx y hy`. Introduce `hx`. Establish `hxX : x ∈ X`.

Rewrite using `[hX]`. Introduce `z hz`. Use `hx (p • z) ((h1 z).2 hz)` as an intermediate fact. Rewrite `this` using `[hBn2, Nat.cast_mul]`. Conclude with `(mul_dvd_mul_iff_left hp').1 this`.

Take `⟨l, hl⟩` from `kX b hb x hxX`. Establish `hlL : l ∈ L`. Apply `hdd` to reduce the goal to its premises. Introduce `y hy`. Take `⟨w, hw⟩` from `kX b hb y hy`.

Establish `hby : b • y ∈ N` using `(hN _).2 ⟨b • w, hL b hb w, b • y, X.smul_mem b hy, by`. Combine the equalities or inequalities in the displayed calculation. Establish `e : B x (b • y) = p * B l y`. Rewrite using `[← hBn, ← hl, hsesq, hσ]`. Use `hx (b • y) hby` as an intermediate fact.

Rewrite `this` using `[e, Nat.cast_mul]`. Conclude with `(mul_dvd_mul_iff_left hp').1 this`. Use `show x ∈ N`. Use `(hN x).2 ⟨l, hlL, x, hxX, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Use `⟨N, h1, h2, h3, ?_⟩` and prove the remaining obligations. Establish `o` using `relIndex_orth B hbij (m := p * p) (mul_ne_zero hp hp) N.toAddSubgroup N.toAddSubgroup hKN hself`. Conclude with `Nat.mul_self_inj.1 (o.trans (mul_pow p p _))`.
-/
theorem exists_lagrangian {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [Module.Free ℤ M]
    [Module.Finite ℤ M] {σ : R ≃+* R} {B : M →+ M →+ ℤ} (h : IsUnimod σ B) (P : Ideal R) {a b : R} (ha : a ∈ P)
    (hb : b ∈ P) (hab : a + σ b = 1) (hσ : ∀ a, σ (σ a) = a) {p : ℕ} (hp : p ≠ 0) (hpP : (p : R) ∈ P)
    (L : Submodule R M) (hL : ∀ a ∈ P, ∀ x, a • x ∈ L) :
    ∃ N : Submodule R M, (∀ z, p • z ∈ N ↔ z ∈ L) ∧ (∀ c ∈ P, ∀ x ∈ N, ∃ z, σ c • x = p • z) ∧
      (∀ x ∈ N, ∀ y ∈ N, ((p * p : ℕ) : ℤ) ∣ B x y) ∧
      (nsmulAddMonoidHom (α := M) (p * p)).range.relIndex N.toAddSubgroup = p ^ Module.finrank ℤ M := by
  unfold IsUnimod at h
  obtain ⟨halt, hsesq, hbij⟩ := h
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have hBn : ∀ (k : ℕ) (u y : M), B (k • u) y = k * B u y := by intro k u y; simp [map_nsmul]
  have hBn2 : ∀ (k : ℕ) (u y : M), B u (k • y) = k * B u y := by intro k u y; simp [map_nsmul]
  have hcan : ∀ u v : M, p • u = p • v → u = v := by
    intro u v huv
    apply hbij.1
    ext y
    apply mul_left_cancel₀ hp'
    rw [← hBn, ← hBn, huv]
  have hpL : ∀ z, p • z ∈ L := fun z => by
    rw [← Nat.cast_smul_eq_nsmul R]
    exact hL _ hpP z
  let X : Submodule R M :=
    { carrier := {x | ∀ z ∈ L, (p : ℤ) ∣ B x z}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq] at *
        intro z hz
        simpa using dvd_add (hx z hz) (hy z hz)
      zero_mem' := by
        simp only [Set.mem_ofPred_eq]
        intro z _
        simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_ofPred_eq] at *
        intro z hz
        rw [hsesq]
        exact hx _ (L.smul_mem _ hz) }
  have hX : ∀ x, x ∈ X ↔ ∀ z ∈ L, (p : ℤ) ∣ B x z := fun x => Iff.rfl
  have kX : ∀ c ∈ P, ∀ x ∈ X, ∃ w, σ c • x = p • w := by
    intro c hc x hx
    obtain ⟨w, hw⟩ := exists_nsmul_of_dvd B hbij hp (x := σ c • x) fun y => by
      rw [hsesq, hσ]
      exact (hX x).1 hx _ (hL c hc y)
    exact ⟨w, hw.symm⟩
  let N : Submodule R M :=
    { carrier := {y | ∃ l ∈ L, ∃ x ∈ X, y = p • l + a • x}
      add_mem' := by
        rintro _ _ ⟨l1, hl1, x1, hx1, rfl⟩ ⟨l2, hl2, x2, hx2, rfl⟩
        exact ⟨l1 + l2, L.add_mem hl1 hl2, x1 + x2, X.add_mem hx1 hx2, by rw [smul_add, smul_add]; abel⟩
      zero_mem' := ⟨0, L.zero_mem, 0, X.zero_mem, by simp⟩
      smul_mem' := by
        rintro c _ ⟨l, hl, x, hx, rfl⟩
        exact ⟨c • l, L.smul_mem c hl, c • x, X.smul_mem c hx, by
          rw [smul_add, smul_comm c p l, smul_comm c a x]⟩ }
  have hN : ∀ y, y ∈ N ↔ ∃ l ∈ L, ∃ x ∈ X, y = p • l + a • x := fun y => Iff.rfl
  have h1 : ∀ z, p • z ∈ N ↔ z ∈ L := by
    intro z
    rw [hN]
    constructor
    · rintro ⟨l, hl, x, hx, e⟩
      obtain ⟨w', hw'⟩ := kX b hb x hx
      have hw : p • (z - l) = a • x := by rw [smul_sub, e]; abel
      have hs : σ b • (z - l) = a • w' := by
        apply hcan
        rw [smul_comm p (σ b) (z - l), hw, smul_comm (σ b) a x, hw', smul_comm a p w']
      have hzl : z - l ∈ L := by
        have e2 : z - l = a • (z - l) + σ b • (z - l) := by rw [← add_smul, hab, one_smul]
        rw [e2, hs]
        exact L.add_mem (hL a ha _) (hL a ha _)
      simpa using L.add_mem hzl hl
    · intro hz
      exact ⟨z, hz, 0, X.zero_mem, by simp⟩
  have h2 : ∀ c ∈ P, ∀ x ∈ N, ∃ z, σ c • x = p • z := by
    intro c hc y hy
    obtain ⟨l, hl, x, hx, rfl⟩ := (hN y).1 hy
    obtain ⟨w, hw⟩ := kX c hc x hx
    exact ⟨σ c • l + a • w, by
      rw [smul_add, smul_add, smul_comm (σ c) p l, smul_comm (σ c) a x, hw, smul_comm a p w]⟩
  have h3 : ∀ x ∈ N, ∀ y ∈ N, ((p * p : ℕ) : ℤ) ∣ B x y := by
    intro x hx y hy
    obtain ⟨l1, hl1, x1, hx1, rfl⟩ := (hN x).1 hx
    obtain ⟨l2, hl2, x2, hx2, rfl⟩ := (hN y).1 hy
    obtain ⟨w, hw⟩ := kX a ha x2 hx2
    obtain ⟨k1, hk1⟩ : (p : ℤ) ∣ B (a • x2) l1 := (hX _).1 (X.smul_mem a hx2) l1 hl1
    obtain ⟨k2, hk2⟩ : (p : ℤ) ∣ B (a • x1) l2 := (hX _).1 (X.smul_mem a hx1) l2 hl2
    obtain ⟨k3, hk3⟩ : (p : ℤ) ∣ B x1 (a • w) := (hX _).1 hx1 _ (hL a ha w)
    have e4 : B (a • x1) (a • x2) = p * B x1 (a • w) := by
      rw [hsesq, smul_comm (σ a) a x2, hw, smul_comm a p w, hBn2]
    have e2 : B l1 (a • x2) = - B (a • x2) l1 := by rw [halt]
    refine ⟨B l1 l2 - k1 + k2 + k3, ?_⟩
    simp only [map_add, AddMonoidHom.add_apply, hBn, hBn2, e4, e2, hk1, hk2, hk3]
    push_cast
    ring
  have hdd : ∀ l : M, (∀ y ∈ X, (p : ℤ) ∣ B l y) → l ∈ L := by
    have hKL : (nsmulAddMonoidHom (α := M) p).range ≤ L.toAddSubgroup := by
      rintro _ ⟨w, rfl⟩
      exact hpL w
    have hKX : (nsmulAddMonoidHom (α := M) p).range ≤ X.toAddSubgroup := by
      rintro _ ⟨w, rfl⟩
      show p • w ∈ X
      rw [hX]
      intro z _
      rw [hBn]
      exact dvd_mul_right _ _
    let L2 : AddSubgroup M :=
      { carrier := {l | ∀ y ∈ X, (p : ℤ) ∣ B l y}
        add_mem' := by
          intro u v hu hv
          simp only [Set.mem_ofPred_eq] at *
          intro y hy
          simpa using dvd_add (hu y hy) (hv y hy)
        zero_mem' := by
          simp only [Set.mem_ofPred_eq]
          intro y _
          simp
        neg_mem' := by
          intro u hu
          simp only [Set.mem_ofPred_eq] at *
          intro y hy
          simpa using (hu y hy).neg_right }
    have o1 : (nsmulAddMonoidHom (α := M) p).range.relIndex L.toAddSubgroup *
        (nsmulAddMonoidHom (α := M) p).range.relIndex X.toAddSubgroup = p ^ Module.finrank ℤ M :=
      relIndex_orth B hbij hp L.toAddSubgroup X.toAddSubgroup hKL (fun x => hX x)
    have o2 : (nsmulAddMonoidHom (α := M) p).range.relIndex X.toAddSubgroup *
        (nsmulAddMonoidHom (α := M) p).range.relIndex L2 = p ^ Module.finrank ℤ M :=
      relIndex_orth B hbij hp X.toAddSubgroup L2 hKX (fun x => Iff.rfl)
    have hLL2 : L.toAddSubgroup ≤ L2 := by
      intro l hl
      show ∀ y ∈ X, (p : ℤ) ∣ B l y
      intro y hy
      rw [halt]
      exact ((hX y).1 hy l hl).neg_right
    have o3 := AddSubgroup.relIndex_mul_relIndex _ _ _ hKL hLL2
    have hX0 : (nsmulAddMonoidHom (α := M) p).range.relIndex X.toAddSubgroup ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at o2
      exact pow_ne_zero _ hp o2.symm
    have hL0 : (nsmulAddMonoidHom (α := M) p).range.relIndex L.toAddSubgroup ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at o1
      exact pow_ne_zero _ hp o1.symm
    have eq12 : (nsmulAddMonoidHom (α := M) p).range.relIndex L.toAddSubgroup =
        (nsmulAddMonoidHom (α := M) p).range.relIndex L2 := by
      apply mul_right_cancel₀ hX0
      rw [o1, mul_comm, o2]
    have hone : L.toAddSubgroup.relIndex L2 = 1 := by
      apply mul_left_cancel₀ hL0
      rw [o3, Nat.mul_one, eq12]
    intro l hl
    exact AddSubgroup.relIndex_eq_one.1 hone hl
  have hKN : (nsmulAddMonoidHom (α := M) (p * p)).range ≤ N.toAddSubgroup := by
    rintro _ ⟨w, rfl⟩
    show (p * p) • w ∈ N
    rw [mul_smul]
    exact (h1 _).2 (hpL w)
  have hself : ∀ x, x ∈ N.toAddSubgroup ↔ ∀ y ∈ N.toAddSubgroup, ((p * p : ℕ) : ℤ) ∣ B x y := by
    intro x
    constructor
    · intro hx y hy
      exact h3 x hx y hy
    · intro hx
      have hxX : x ∈ X := by
        rw [hX]
        intro z hz
        have := hx (p • z) ((h1 z).2 hz)
        rw [hBn2, Nat.cast_mul] at this
        exact (mul_dvd_mul_iff_left hp').1 this
      obtain ⟨l, hl⟩ := kX b hb x hxX
      have hlL : l ∈ L := by
        apply hdd
        intro y hy
        obtain ⟨w, hw⟩ := kX b hb y hy
        have hby : b • y ∈ N := (hN _).2 ⟨b • w, hL b hb w, b • y, X.smul_mem b hy, by
          calc b • y = a • (b • y) + σ b • (b • y) := by rw [← add_smul, hab, one_smul]
            _ = p • (b • w) + a • (b • y) := by rw [smul_comm (σ b) b y, hw, smul_comm b p w, add_comm]⟩
        have e : B x (b • y) = p * B l y := by
          rw [← hBn, ← hl, hsesq, hσ]
        have := hx (b • y) hby
        rw [e, Nat.cast_mul] at this
        exact (mul_dvd_mul_iff_left hp').1 this
      show x ∈ N
      refine (hN x).2 ⟨l, hlL, x, hxX, ?_⟩
      calc x = a • x + σ b • x := by rw [← add_smul, hab, one_smul]
        _ = p • l + a • x := by rw [hl, add_comm]
  refine ⟨N, h1, h2, h3, ?_⟩
  have o := relIndex_orth B hbij (m := p * p) (mul_ne_zero hp hp) N.toAddSubgroup N.toAddSubgroup hKN hself
  exact Nat.mul_self_inj.1 (o.trans (mul_pow p p _))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

/- English proof (translation)
Set `f : A →+ Additive Q` to `(GlobalTheory.HeckeTate.evHom I n).comp A.subtype`. Establish `hker : f.ker = (nsmulAddMonoidHom (α` using `D.La) n).range.addSubgroupOf A := by`. Use extensionality with `a`. Rewrite using `[AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]`. Express the relevant statement in the definitionally equal form `Additive.ofMul (I.ev n a) = Additive.ofMul 1 ↔ _`.

Rewrite using `[Additive.ofMul.injective.eq_iff, I.ker n hn]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb⟩`. Conclude with `⟨b, hb.symm⟩`. Introduce and unpack `⟨b, hb⟩`.

Conclude with `⟨b, hb.symm⟩`. Rewrite using `[AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker]`. Use `Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun x => ?_)` and prove the remaining obligations. Rewrite using `[hs x, AddMonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `⟨⟨a, ha⟩, rfl⟩`. Introduce and unpack `⟨⟨a, ha⟩, h⟩`. Conclude with `⟨a, ha, Additive.ofMul.injective h⟩`.
-/
theorem card_image_ev {k : Type} [Field k] {Q : Type} [CommGroup Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (A : AddSubgroup D.La) (s : Set Q)
    (hs : ∀ x, x ∈ s ↔ ∃ a ∈ A, I.ev n a = x) :
    Nat.card s = (nsmulAddMonoidHom (α := D.La) n).range.relIndex A := by
  classical
  let f : A →+ Additive Q := (GlobalTheory.HeckeTate.evHom I n).comp A.subtype
  have hker : f.ker = (nsmulAddMonoidHom (α := D.La) n).range.addSubgroupOf A := by
    ext a
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
    change Additive.ofMul (I.ev n a) = Additive.ofMul 1 ↔ _
    rw [Additive.ofMul.injective.eq_iff, I.ker n hn]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b, hb.symm⟩
    · rintro ⟨b, hb⟩
      exact ⟨b, hb.symm⟩
  rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker]
  refine Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun x => ?_)
  rw [hs x, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨⟨a, ha⟩, h⟩
    exact ⟨a, ha, Additive.ofMul.injective h⟩

/- English proof (translation)
Take `⟨-, I, -, -, -⟩` from `o.geom k x β hx`. Establish `: Module.Finite (𝓞 E) D.La` using `D.fin`. Establish `: Module.Projective (𝓞 E) D.La` using `D.proj`. Establish `: Module.Free ℤ D.La` using `GlobalTheory.datum_free_int D`. Establish `: Module.Finite ℤ D.La` using `Module.Finite.trans (𝓞 E) D.La`.

Establish `hrk` using `GlobalTheory.datum_finrank_int D`. Establish `hp0 : p ≠ 0` using `hp.ne'`. Establish `hp' : (p : ℤ) ≠ 0` using `by exact_mod_cast hp0`. Establish `hpp : 0 < p * p` using `Nat.mul_pos hp hp`. Establish `hU` using `GlobalTheory.HeckeTate.form_isUnimod D`.

Establish `hU'` using `hU`. Unfold `IsUnimod at hU'`. Take `⟨-, -, hbij⟩` from `hU'`. Establish `hcan : ∀ u v : D.La, p • u = p • v → u = v`. Introduce `u v huv`.

Apply `hbij.1` to reduce the goal to its premises. Use extensionality with `y`. Apply `mul_left_cancel₀ hp'` to reduce the goal to its premises. Use `congrArg (fun z => GlobalTheory.HeckeTate.form D z y) huv` as an intermediate fact. Simplify `this` using `[map_nsmul]`.

Take `⟨a, ha, c, hc, hac⟩` from `Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ P ⊔ Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) P by rw [hPP]; exact Submodule.mem_top)`. Rewrite `hc` using `[Ideal.map_comap_of_equiv]`. Establish `hb : H.bar.symm c ∈ P` using `hc`. Establish `hab : a + H.bar (H.bar.symm c) = 1` using `by rw [RingEquiv.apply_symm_apply]; exact hac`. Take `⟨L, hL, hLi⟩` from `exists_sublattice (R := 𝓞 E) (M := D.La) P hP (i := i) (by rw [D.rank]; exact hi)`.

Take `⟨N, hN1, hN2, hN3, hN4⟩` from `exists_lagrangian hU P ha hb hab (GlobalTheory.HeckeTate.bar_bar H) hp0 hpP L hL`. Establish `hpL : ∀ z : D.La, p • z ∈ L` using `fun z => by`. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E)]`. Conclude with `hL _ hpP z`. Set `C : Subgroup (Over.mk x ⟶ o.t.G)` to `{ carrier := {g | ∃ y ∈ N, I.ev (p * p) y = g} mul_mem' := by`.

Introduce and unpack `_ _ ⟨a1, h1, rfl⟩ ⟨a2, h2, rfl⟩`. Conclude with `⟨a1 + a2, N.add_mem h1 h2, I.add _ _ _⟩`. Use the proof step `one_mem' := ⟨0, N.zero_mem, GlobalTheory.HeckeTate.ev_zero I _⟩`. Use the proof step `inv_mem' := by`. Introduce and unpack `_ ⟨a1, h1, rfl⟩`.

Use `⟨-a1, N.neg_mem h1, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_inv_iff_mul_eq_one, ← I.add, neg_add_cancel, GlobalTheory.HeckeTate.ev_zero] }`. Establish `hC : ∀ g, g ∈ C ↔ ∃ y ∈ N, I.ev (p * p) y = g` using `fun g => Iff.rfl`. Use `⟨C, ?_⟩` and prove the remaining obligations. Unfold `SAB.HeckeKer`.

Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg d`. Take `⟨y, hy, rfl⟩` from `(hC g).1 hg`. Conclude with `(hC _).2 ⟨d • y, N.smul_mem d hy, I.lin _ _ _⟩`. Introduce `J hJ g hg`.

Establish `hg' : ∀ d ∈ J, g ≫ o.t.act.act d = 1` using `hg`. Establish `hpJP : (p : 𝓞 E) ∈ J * P` using `by rw [hJ]; exact Ideal.mem_span_singleton_self _`. Establish `hpJ : (p : 𝓞 E) ∈ J` using `Ideal.mul_le_left hpJP`. Establish `hgp : g ^ p = 1`. Rewrite using `[← GlobalTheory.HeckeKerModel.comp_act_natCast]`.

Conclude with `hg' _ hpJ`. Take `⟨a', ha'⟩` from `(I.onto p hp g).1 hgp`. Establish `hgE : I.ev (p * p) (p • a') = g`. Rewrite using `[GlobalTheory.HeckeTate.ev_nsmul, I.tower p p hp hp, ha']`. Establish `hJa : ∀ d ∈ J, ∃ w, d • a' = p • w`.

Introduce `d hd`. Establish `h0 : I.ev (p * p) (d • (p • a')) = 1`. Rewrite using `[I.lin, hgE]`. Conclude with `hg' d hd`. Take `⟨b', hb'⟩` from `(I.ker (p * p) hpp _).1 h0`.

Use `⟨b', hcan _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_comm d p a', hb', mul_smul]`. Establish `key : ∀ r ∈ J * P, ∃ y ∈ L, r • a' = p • y`. Introduce `r hr`. Use `Submodule.mul_induction_on (C := fun r => ∃ y ∈ L, r • a' = p • y) hr ?_ ?_` and prove the remaining obligations.

Introduce `d hd e he`. Take `⟨w, hw⟩` from `hJa d hd`. Use `⟨e • w, hL e he w, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul, hw, smul_comm e p w]`. Introduce and unpack `r1 r2 ⟨y1, hy1, e1⟩ ⟨y2, hy2, e2⟩`.

Conclude with `⟨y1 + y2, L.add_mem hy1 hy2, by rw [add_smul, e1, e2, smul_add]⟩`. Take `⟨y, hy, hyeq⟩` from `key (p : 𝓞 E) hpJP`. Rewrite `hyeq` using `[Nat.cast_smul_eq_nsmul]`. Establish `ha'L : a' ∈ L` using `(hcan _ _ hyeq) ▸ hy`. Conclude with `(hC g).2 ⟨p • a', (hN1 a').2 ha'L, hgE⟩`.

Introduce `g hg d hd`. Take `⟨y, hy, rfl⟩` from `(hC g).1 hg`. Use `show I.ev (p * p) y ≫ o.t.act.act d = 1`. Rewrite using `[← I.lin, I.ker (p * p) hpp]`. Use `Submodule.mul_induction_on (C := fun r => ∃ b, r • y = (p * p) • b) hd ?_ ?_` and prove the remaining obligations.

Introduce `r hr e he`. Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.1 hr`. Rewrite `he` using `[Ideal.map_comap_of_equiv]`. Establish `he' : H.bar.symm e ∈ P` using `he`. Take `⟨z, hz⟩` from `hN2 _ he' y hy`.

Rewrite `hz` using `[RingEquiv.apply_symm_apply]`. Use `⟨t • z, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hz, Nat.cast_smul_eq_nsmul, smul_comm t p (p • z), smul_comm t p z, mul_smul]`. Introduce and unpack `r1 r2 ⟨b1, e1⟩ ⟨b2, e2⟩`.

Conclude with `⟨b1 + b2, by rw [add_smul, e1, e2, smul_add]⟩`. Introduce `g hg g' hg'`. Take `⟨y1, hy1, rfl⟩` from `(hC g).1 hg`. Take `⟨y2, hy2, rfl⟩` from `(hC g').1 hg'`. Establish `hw` using `I.isom (p * p) hpp y1 y2`.

Take `⟨k3, hk3⟩` from `hN3 y1 hy1 y2 hy2`. Rewrite `hk3` using `[GlobalTheory.HeckeTate.form_apply]`. Establish `hz : I.ζ (p * p) ^ (D.EF y1 y2) = 1`. Rewrite using `[hk3, zpow_mul, zpow_natCast, (I.ζ_prim (p * p) hpp).pow_eq_one, one_zpow]`. Rewrite `hw` using `[hz]`.

Apply the tactic sequence `convert hw using 1 <;> first | (push_cast; ring) | (symm; exact map_one _)`. Rewrite using `[show Nat.card C = Nat.card (C : Set (Over.mk x ⟶ o.t.G)) from rfl, card_image_ev I hpp N.toAddSubgroup _ (fun g => hC g), hN4, hrk]`. Establish `hT : ∀ g, g ∈ o.t.tors (Over.mk x) (Ideal.span {(p : 𝓞 E)}) ↔ ∃ a ∈ (⊤ : AddSubgroup D.La), I.ev p a = g`. Introduce `g`. Rewrite using `[GlobalTheory.HeckeKerModel.mem_tors_span, I.onto p hp]`.

Simplify using the standard rewrite rules. Establish `hCT : ∀ g, g ∈ (C : Set (Over.mk x ⟶ o.t.G)) ∩ o.t.tors (Over.mk x) (Ideal.span {(p : 𝓞 E)}) ↔ ∃ a ∈ L.toAddSubgroup, I.ev p a = g`. Introduce `g`. Rewrite using `[Set.mem_inter_iff, GlobalTheory.HeckeKerModel.mem_tors_span]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hg, hgp⟩`. Take `⟨y, hy, rfl⟩` from `(hC _).1 hg`. Rewrite `hgp` using `[← GlobalTheory.HeckeTate.ev_nsmul, I.ker _ hpp]`. Take `⟨b', hb'⟩` from `hgp`. Establish `hyb : y = p • b'` using `hcan _ _ (by rw [hb', mul_smul])`.

Substitute `hyb` using the available equality. Conclude with `⟨b', (hN1 b').1 hy, by rw [GlobalTheory.HeckeTate.ev_nsmul, I.tower p p hp hp]⟩`. Introduce and unpack `⟨z, hz, rfl⟩`. Use `⟨(hC _).2 ⟨p • z, (hN1 z).2 hz, by rw [GlobalTheory.HeckeTate.ev_nsmul, I.tower p p hp hp]⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← GlobalTheory.HeckeTate.ev_nsmul, I.ker p hp]`.

Conclude with `⟨z, rfl⟩`. Establish `hKL : (nsmulAddMonoidHom (α` using `D.La) p).range ≤ L.toAddSubgroup := by`. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `hpL w`. Rewrite using `[card_image_ev I hp ⊤ _ hT, card_image_ev I hp L.toAddSubgroup _ hCT, AddSubgroup.relIndex_top_right, Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hLi, AddSubgroup.relIndex_mul_index hKL]`.
-/
theorem exists_heckeKer_obj {S : Scheme.{0}} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {s : S ⟶ Sp B}
    (o : Obj D l b s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (hx : x ≫ s = spMap β)
    (P : Ideal (𝓞 E)) (p i : ℕ) (hP : P.IsMaximal) (hPP : P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (hp : 0 < p)
    (hpP : (p : 𝓞 E) ∈ P) (hi : i ≤ D.p + D.q) : ∃ C, o.t.HeckeKer (Over.mk x) D P p i C := by
  classical
  obtain ⟨-, I, -, -, -⟩ := o.geom k x β hx
  have : Module.Finite (𝓞 E) D.La := D.fin
  have : Module.Projective (𝓞 E) D.La := D.proj
  have : Module.Free ℤ D.La := GlobalTheory.datum_free_int D
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have hrk := GlobalTheory.datum_finrank_int D
  have hp0 : p ≠ 0 := hp.ne'
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp0
  have hpp : 0 < p * p := Nat.mul_pos hp hp
  have hU := GlobalTheory.HeckeTate.form_isUnimod D
  have hU' := hU
  unfold IsUnimod at hU'
  obtain ⟨-, -, hbij⟩ := hU'
  have hcan : ∀ u v : D.La, p • u = p • v → u = v := by
    intro u v huv
    apply hbij.1
    ext y
    apply mul_left_cancel₀ hp'
    have := congrArg (fun z => GlobalTheory.HeckeTate.form D z y) huv
    simpa [map_nsmul] using this
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.1
    (show (1 : 𝓞 E) ∈ P ⊔ Ideal.map (H.bar : 𝓞 E →+* 𝓞 E) P by rw [hPP]; exact Submodule.mem_top)
  rw [Ideal.map_comap_of_equiv] at hc
  have hb : H.bar.symm c ∈ P := hc
  have hab : a + H.bar (H.bar.symm c) = 1 := by rw [RingEquiv.apply_symm_apply]; exact hac
  obtain ⟨L, hL, hLi⟩ := exists_sublattice (R := 𝓞 E) (M := D.La) P hP (i := i) (by rw [D.rank]; exact hi)
  obtain ⟨N, hN1, hN2, hN3, hN4⟩ := exists_lagrangian hU P ha hb hab (GlobalTheory.HeckeTate.bar_bar H) hp0 hpP L hL
  have hpL : ∀ z : D.La, p • z ∈ L := fun z => by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact hL _ hpP z
  let C : Subgroup (Over.mk x ⟶ o.t.G) :=
    { carrier := {g | ∃ y ∈ N, I.ev (p * p) y = g}
      mul_mem' := by
        rintro _ _ ⟨a1, h1, rfl⟩ ⟨a2, h2, rfl⟩
        exact ⟨a1 + a2, N.add_mem h1 h2, I.add _ _ _⟩
      one_mem' := ⟨0, N.zero_mem, GlobalTheory.HeckeTate.ev_zero I _⟩
      inv_mem' := by
        rintro _ ⟨a1, h1, rfl⟩
        refine ⟨-a1, N.neg_mem h1, ?_⟩
        rw [eq_inv_iff_mul_eq_one, ← I.add, neg_add_cancel, GlobalTheory.HeckeTate.ev_zero] }
  have hC : ∀ g, g ∈ C ↔ ∃ y ∈ N, I.ev (p * p) y = g := fun g => Iff.rfl
  refine ⟨C, ?_⟩
  unfold SAB.HeckeKer
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg d
    obtain ⟨y, hy, rfl⟩ := (hC g).1 hg
    exact (hC _).2 ⟨d • y, N.smul_mem d hy, I.lin _ _ _⟩
  · intro J hJ g hg
    have hg' : ∀ d ∈ J, g ≫ o.t.act.act d = 1 := hg
    have hpJP : (p : 𝓞 E) ∈ J * P := by rw [hJ]; exact Ideal.mem_span_singleton_self _
    have hpJ : (p : 𝓞 E) ∈ J := Ideal.mul_le_left hpJP
    have hgp : g ^ p = 1 := by
      rw [← GlobalTheory.HeckeKerModel.comp_act_natCast]
      exact hg' _ hpJ
    obtain ⟨a', ha'⟩ := (I.onto p hp g).1 hgp
    have hgE : I.ev (p * p) (p • a') = g := by
      rw [GlobalTheory.HeckeTate.ev_nsmul, I.tower p p hp hp, ha']
    have hJa : ∀ d ∈ J, ∃ w, d • a' = p • w := by
      intro d hd
      have h0 : I.ev (p * p) (d • (p • a')) = 1 := by
        rw [I.lin, hgE]
        exact hg' d hd
      obtain ⟨b', hb'⟩ := (I.ker (p * p) hpp _).1 h0
      refine ⟨b', hcan _ _ ?_⟩
      rw [← smul_comm d p a', hb', mul_smul]
    have key : ∀ r ∈ J * P, ∃ y ∈ L, r • a' = p • y := by
      intro r hr
      refine Submodule.mul_induction_on (C := fun r => ∃ y ∈ L, r • a' = p • y) hr ?_ ?_
      · intro d hd e he
        obtain ⟨w, hw⟩ := hJa d hd
        refine ⟨e • w, hL e he w, ?_⟩
        rw [mul_comm, mul_smul, hw, smul_comm e p w]
      · rintro r1 r2 ⟨y1, hy1, e1⟩ ⟨y2, hy2, e2⟩
        exact ⟨y1 + y2, L.add_mem hy1 hy2, by rw [add_smul, e1, e2, smul_add]⟩
    obtain ⟨y, hy, hyeq⟩ := key (p : 𝓞 E) hpJP
    rw [Nat.cast_smul_eq_nsmul] at hyeq
    have ha'L : a' ∈ L := (hcan _ _ hyeq) ▸ hy
    exact (hC g).2 ⟨p • a', (hN1 a').2 ha'L, hgE⟩
  · intro g hg d hd
    obtain ⟨y, hy, rfl⟩ := (hC g).1 hg
    show I.ev (p * p) y ≫ o.t.act.act d = 1
    rw [← I.lin, I.ker (p * p) hpp]
    refine Submodule.mul_induction_on (C := fun r => ∃ b, r • y = (p * p) • b) hd ?_ ?_
    · intro r hr e he
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [Ideal.map_comap_of_equiv] at he
      have he' : H.bar.symm e ∈ P := he
      obtain ⟨z, hz⟩ := hN2 _ he' y hy
      rw [RingEquiv.apply_symm_apply] at hz
      refine ⟨t • z, ?_⟩
      calc (t * ↑p * e) • y = t • ((p : 𝓞 E) • (e • y)) := by rw [mul_smul, mul_smul]
        _ = (p * p) • (t • z) := by
          rw [hz, Nat.cast_smul_eq_nsmul, smul_comm t p (p • z), smul_comm t p z, mul_smul]
    · rintro r1 r2 ⟨b1, e1⟩ ⟨b2, e2⟩
      exact ⟨b1 + b2, by rw [add_smul, e1, e2, smul_add]⟩
  · intro g hg g' hg'
    obtain ⟨y1, hy1, rfl⟩ := (hC g).1 hg
    obtain ⟨y2, hy2, rfl⟩ := (hC g').1 hg'
    have hw := I.isom (p * p) hpp y1 y2
    obtain ⟨k3, hk3⟩ := hN3 y1 hy1 y2 hy2
    rw [GlobalTheory.HeckeTate.form_apply] at hk3
    have hz : I.ζ (p * p) ^ (D.EF y1 y2) = 1 := by
      rw [hk3, zpow_mul, zpow_natCast, (I.ζ_prim (p * p) hpp).pow_eq_one, one_zpow]
    rw [hz] at hw
    convert hw using 1 <;> first | (push_cast; ring) | (symm; exact map_one _)
  · rw [show Nat.card C = Nat.card (C : Set (Over.mk x ⟶ o.t.G)) from rfl,
      card_image_ev I hpp N.toAddSubgroup _ (fun g => hC g), hN4, hrk]
  · have hT : ∀ g, g ∈ o.t.tors (Over.mk x) (Ideal.span {(p : 𝓞 E)}) ↔
        ∃ a ∈ (⊤ : AddSubgroup D.La), I.ev p a = g := by
      intro g
      rw [GlobalTheory.HeckeKerModel.mem_tors_span, I.onto p hp]
      simp
    have hCT : ∀ g, g ∈ (C : Set (Over.mk x ⟶ o.t.G)) ∩ o.t.tors (Over.mk x) (Ideal.span {(p : 𝓞 E)}) ↔
        ∃ a ∈ L.toAddSubgroup, I.ev p a = g := by
      intro g
      rw [Set.mem_inter_iff, GlobalTheory.HeckeKerModel.mem_tors_span]
      constructor
      · rintro ⟨hg, hgp⟩
        obtain ⟨y, hy, rfl⟩ := (hC _).1 hg
        rw [← GlobalTheory.HeckeTate.ev_nsmul, I.ker _ hpp] at hgp
        obtain ⟨b', hb'⟩ := hgp
        have hyb : y = p • b' := hcan _ _ (by rw [hb', mul_smul])
        subst hyb
        exact ⟨b', (hN1 b').1 hy, by rw [GlobalTheory.HeckeTate.ev_nsmul, I.tower p p hp hp]⟩
      · rintro ⟨z, hz, rfl⟩
        refine ⟨(hC _).2 ⟨p • z, (hN1 z).2 hz, by rw [GlobalTheory.HeckeTate.ev_nsmul, I.tower p p hp hp]⟩, ?_⟩
        rw [← GlobalTheory.HeckeTate.ev_nsmul, I.ker p hp]
        exact ⟨z, rfl⟩
    have hKL : (nsmulAddMonoidHom (α := D.La) p).range ≤ L.toAddSubgroup := by
      rintro _ ⟨w, rfl⟩
      exact hpL w
    rw [card_image_ev I hp ⊤ _ hT, card_image_ev I hp L.toAddSubgroup _ hCT,
      AddSubgroup.relIndex_top_right, Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hLi,
      AddSubgroup.relIndex_mul_index hKL]

end GlobalTheory.HeckeKerAll

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ H D l Xo 𝔓 p i h1 h2 h3 h4 h5 k _ _ y`. Take `⟨C, hC⟩` from `GlobalTheory.HeckeKerAll.exists_heckeKer_obj Xo.univ k y (Spec.preimage (y ≫ Xo.s)).hom (Spec.map_preimage _).symm 𝔓 p i h1 h2 h3.pos h4 h5`. Conclude with `⟨C, hC⟩`.
-/
theorem exists_heckeKer :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), 𝔓.IsMaximal → 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → p.Prime → (p : 𝓞 E) ∈ 𝔓 → i ≤ D.p + D.q → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X), ∃ C : Subgroup (Over.mk y ⟶ Xo.univ.t.G), Xo.univ.t.HeckeKer (Over.mk y) D 𝔓 p i C := by
  intro E _ _ _ H D l Xo 𝔓 p i h1 h2 h3 h4 h5 k _ _ y
  obtain ⟨C, hC⟩ := GlobalTheory.HeckeKerAll.exists_heckeKer_obj Xo.univ k y (Spec.preimage (y ≫ Xo.s)).hom
    (Spec.map_preimage _).symm 𝔓 p i h1 h2 h3.pos h4 h5
  exact ⟨C, hC⟩

end GlobalTheory
