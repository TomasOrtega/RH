import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ExistsAvg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.HeckeMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.JacNorm

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

/- English proof (translation)
Use `set c : Fin n → kˣ := fun i => if valuation k ((t i : kˣ) : k) ≤ 1 then (t i)⁻¹ else t i with hc`. Establish `hv : ∀ u : kˣ, valuation k (u : k) ≠ 0` using `fun u => by simp`. Establish `hc1 : ∀ i, 1 ≤ valuation k ((c i : kˣ) : k)`. Introduce `i`. Simplify using `only [hc]`.

Use `split_ifs with h`. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀]`. Conclude with `one_le_inv_iff₀.mpr ⟨zero_lt_iff.mpr (hv _), h⟩`. Conclude with `le_of_lt (not_le.mp h)`. Establish `hct : ∀ i, valuation k ((t i : kˣ) : k) ≤ valuation k ((c i : kˣ) : k)`.

Introduce `i`. Simplify using `only [hc]`. Use `split_ifs with h`. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀]`. Conclude with `h.trans (one_le_inv_iff₀.mpr ⟨zero_lt_iff.mpr (hv _), h⟩)`.

Conclude with `le_rfl`. Establish `hct' : ∀ i, (valuation k ((t i : kˣ) : k))⁻¹ ≤ valuation k ((c i : kˣ) : k)`. Introduce `i`. Simplify using `only [hc]`. Use `split_ifs with h`.

Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀]`. Conclude with `(inv_le_one₀ (zero_lt_iff.mpr (hv _))).mpr (le_of_lt (not_le.mp h)) |>.trans (le_of_lt (not_le.mp h))`. Use `set x : kˣ := ∏ i, c i with hx`. Establish `hx1 : 1 ≤ valuation k (x : k)`. Rewrite using `[hx, Units.coe_prod, map_prod]`.

Conclude with `Finset.one_le_prod' (fun i _ => hc1 i)`. Establish `hx2 : ∀ i j, i ≠ j → valuation k ((c i : kˣ) : k) * valuation k ((c j : kˣ) : k) ≤ valuation k (x : k)`. Introduce `i j hij`. Rewrite using `[hx, Units.coe_prod, map_prod, ← Finset.prod_pair (f := fun l => valuation k ((c l : kˣ) : k)) hij]`. Conclude with `Finset.prod_le_prod_of_subset_of_one_le' (Finset.subset_univ _) (fun l _ _ => hc1 l)`.

Use `⟨fun i => x ^ (i : ℕ), ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Simplify using `only [Units.val_pow_eq_pow_val, map_pow]`. Conclude with `pow_le_pow_right₀ hx1 (le_of_lt hij)`. Introduce `i j hij`.

Simplify using `only [Pi.mul_apply, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]`. Establish `hle : (i : ℕ) + 1 ≤ (j : ℕ)` using `hij`. Take `⟨m, hm⟩` from `Nat.exists_eq_add_of_le hle`. Rewrite using `[hm, pow_add, pow_add, pow_one, mul_assoc, mul_assoc]`. Use `mul_le_mul_right ?_ _` and prove the remaining obligations.

Establish `h1 : valuation k (x : k) ≤ valuation k (x : k) ^ m * valuation k (x : k)` using `le_mul_of_one_le_left' (one_le_pow₀ hx1)`. Establish `h2 : valuation k ((t i : kˣ) : k) ≤ valuation k (x : k) * valuation k ((t j : kˣ) : k)`. Establish `hne : i ≠ j` using `ne_of_lt hij`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_comm (valuation k (x : k) ^ m), mul_assoc]`.
-/
private theorem exists_dom {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ s : Fin n → kˣ, Dom s ∧ Dom (s * t) := by
  classical
  set c : Fin n → kˣ := fun i => if valuation k ((t i : kˣ) : k) ≤ 1 then (t i)⁻¹ else t i with hc
  have hv : ∀ u : kˣ, valuation k (u : k) ≠ 0 := fun u => by simp
  have hc1 : ∀ i, 1 ≤ valuation k ((c i : kˣ) : k) := by
    intro i
    simp only [hc]
    split_ifs with h
    · rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact one_le_inv_iff₀.mpr ⟨zero_lt_iff.mpr (hv _), h⟩
    · exact le_of_lt (not_le.mp h)
  have hct : ∀ i, valuation k ((t i : kˣ) : k) ≤ valuation k ((c i : kˣ) : k) := by
    intro i
    simp only [hc]
    split_ifs with h
    · rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact h.trans (one_le_inv_iff₀.mpr ⟨zero_lt_iff.mpr (hv _), h⟩)
    · exact le_rfl
  have hct' : ∀ i, (valuation k ((t i : kˣ) : k))⁻¹ ≤ valuation k ((c i : kˣ) : k) := by
    intro i
    simp only [hc]
    split_ifs with h
    · rw [Units.val_inv_eq_inv_val, map_inv₀]
    · exact (inv_le_one₀ (zero_lt_iff.mpr (hv _))).mpr (le_of_lt (not_le.mp h)) |>.trans
        (le_of_lt (not_le.mp h))
  set x : kˣ := ∏ i, c i with hx
  have hx1 : 1 ≤ valuation k (x : k) := by
    rw [hx, Units.coe_prod, map_prod]
    exact Finset.one_le_prod' (fun i _ => hc1 i)
  have hx2 : ∀ i j, i ≠ j →
      valuation k ((c i : kˣ) : k) * valuation k ((c j : kˣ) : k) ≤ valuation k (x : k) := by
    intro i j hij
    rw [hx, Units.coe_prod, map_prod,
      ← Finset.prod_pair (f := fun l => valuation k ((c l : kˣ) : k)) hij]
    exact Finset.prod_le_prod_of_subset_of_one_le' (Finset.subset_univ _) (fun l _ _ => hc1 l)
  refine ⟨fun i => x ^ (i : ℕ), ?_, ?_⟩
  · intro i j hij
    simp only [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_pow_right₀ hx1 (le_of_lt hij)
  · intro i j hij
    simp only [Pi.mul_apply, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    have hle : (i : ℕ) + 1 ≤ (j : ℕ) := hij
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle
    rw [hm, pow_add, pow_add, pow_one, mul_assoc, mul_assoc]
    refine mul_le_mul_right ?_ _
    have h1 : valuation k (x : k) ≤ valuation k (x : k) ^ m * valuation k (x : k) :=
      le_mul_of_one_le_left' (one_le_pow₀ hx1)
    have h2 : valuation k ((t i : kˣ) : k) ≤ valuation k (x : k) * valuation k ((t j : kˣ) : k) := by
      have hne : i ≠ j := ne_of_lt hij
      calc valuation k ((t i : kˣ) : k)
          = valuation k ((t i : kˣ) : k) * ((valuation k ((t j : kˣ) : k))⁻¹ *
              valuation k ((t j : kˣ) : k)) := by rw [inv_mul_cancel₀ (hv _), mul_one]
        _ = (valuation k ((t i : kˣ) : k) * (valuation k ((t j : kˣ) : k))⁻¹) *
              valuation k ((t j : kˣ) : k) := by rw [mul_assoc]
        _ ≤ (valuation k ((c i : kˣ) : k) * valuation k ((c j : kˣ) : k)) *
              valuation k ((t j : kˣ) : k) :=
            mul_le_mul_left (mul_le_mul' (hct i) (hct' j)) _
        _ ≤ valuation k (x : k) * valuation k ((t j : kˣ) : k) :=
            mul_le_mul_left (hx2 i j hne) _
    calc valuation k ((t i : kˣ) : k)
        ≤ valuation k (x : k) * valuation k ((t j : kˣ) : k) := h2
      _ ≤ (valuation k (x : k) ^ m * valuation k (x : k)) * valuation k ((t j : kˣ) : k) :=
          mul_le_mul_left h1 _
      _ = valuation k (x : k) * (valuation k (x : k) ^ m * valuation k ((t j : kˣ) : k)) := by
          rw [mul_comm (valuation k (x : k) ^ m), mul_assoc]

/- English proof (translation)
Unfold `UpperTheory.Gal.Join.ImStab UpperTheory.Gal.Join.ForRep`. Introduce `k _ _ _ _ n V _ _ π hπ K hK`. Establish `hH0` using `heckeMul`. Establish `hJ0` using `jacNorm`. Unfold `UpperTheory.Gal.Join.HeckeMul UpperTheory.Gal.Join.ForRep at hH0`.

Unfold `UpperTheory.Gal.Join.JacNorm UpperTheory.Gal.Join.ForRep at hJ0`. Establish `hH` using `hH0 k n V π`. Establish `hJ` using `hJ0 k n V π`. Use `beta_reduce at hH hJ`. Establish `hco` using `hK.co`.

Establish `hco' : IsCompact (K : Set (GL (Fin n) k)) ∧ IsOpen (K : Set (GL (Fin n) k))`. Unfold `UpperTheory.ConvolutionTheory.C.CO at hco`. Conclude with `hco`. Take `⟨e, he, hcomm⟩` from `avgEx (GL (Fin n) k) V π hπ.1 K hco`. Unfold `UpperTheory.Gal.Join.imK`.

Use `haveI : FiniteDimensional ℂ (fixed π K) := hπ.2 K hco'.2 hco'.1`. Use `haveI hfd : FiniteDimensional ℂ (Submodule.map (twKer π (unipB k (Fin n)) 1).mkQ (fixed π K)) := Module.Finite.map _ _`. Establish `hD : ∀ t : Fin n → kˣ, Dom t → ∀ y ∈ Submodule.map (twKer π (unipB k (Fin n)) 1).mkQ (fixed π K), jacBU π t y ∈ Submodule.map (twKer π (unipB k (Fin n)) 1).mkQ (fixed π K)`. Introduce `t ht y hy`. Take `⟨v, hv, rfl⟩` from `Submodule.mem_map.mp hy`.

Rewrite using `[← (hH K hK e he t ht v hv).2]`. Conclude with `Submodule.mem_map_of_mem (he.mem _)`. Establish `key : ∀ (s : Fin n → kˣ) (z : Jacquet π (unipB k (Fin n))), jacBU π s⁻¹ (jacBU π s z) = z` using `fun s z => by`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Establish `hU : ∀ t : Fin n → kˣ, ∀ y ∈ Submodule.map (twKer π (unipB k (Fin n)) 1).mkQ (fixed π K), jacBU π t y ∈ Submodule.map (twKer π (unipB k (Fin n)) 1).mkQ (fixed π K)`.

Introduce `t y hy`. Take `⟨s, hs, hst⟩` from `exists_dom t`. Set `f` to `(jacBU π s).restrict (fun z hz => hD s hs z hz)`. Establish `hinj : Function.Injective f`. Introduce `a b hab`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1` using `congrArg (fun z => jacBU π s⁻¹ z) (congrArg Subtype.val hab)`. Simplify `h1` using `[f, LinearMap.restrict_apply, key]`. Establish `hsurj` using `LinearMap.injective_iff_surjective.mp hinj`. Take `⟨z, hz⟩` from `hsurj ⟨_, hD _ hst y hy⟩`.

Establish `hz' : jacBU π s z = jacBU π (s * t) y`. Use `congrArg Subtype.val hz` as an intermediate fact. Simplify `this` using `[f, LinearMap.restrict_apply]`. Establish `h2 : jacBU π s (jacBU π t y) = jacBU π s z`. Rewrite using `[hz', map_mul, Module.End.mul_apply]`.

Establish `h3 : jacBU π t y = z`. Use `congrArg (fun w => jacBU π s⁻¹ w) h2` as an intermediate fact. Simplify `this` using `[key]`. Rewrite using `[h3]`. Conclude with `z.2`.

Use `⟨hfd, ?_, ?_⟩` and prove the remaining obligations. Introduce `t y hy`. Establish `hpos : (0 : ℝ) < √(deltaB t)` using `Real.sqrt_pos.mpr (deltaB_pos t)`. Establish `hne : ((√(deltaB t) : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hpos.ne'`. Establish `h1 : jacB π t y = (((√(deltaB t) : ℝ) : ℂ))⁻¹ • jacBU π t y`.

Rewrite using `[hJ t y, smul_smul, inv_mul_cancel₀ hne, one_smul]`. Rewrite using `[h1]`. Conclude with `Submodule.smul_mem _ _ (hU t y hy)`. Introduce `σ A hA hσ y hy`. Take `⟨v, hv, rfl⟩` from `Submodule.mem_map.mp hy`.

Establish `hinv : ∀ g : GL (Fin n) k, sg σ (sg σ.symm g) = g`. Introduce `g`. Use extensionality with `i j`. Rewrite using `[sg_val, sg_val, RingEquiv.apply_symm_apply]`. Establish `hs1 : ∀ g ∈ K, sg σ g ∈ K` using `fun g hg => (hσ g).mpr hg`.

Establish `hs2 : ∀ g ∈ K, ∃ h ∈ K, sg σ h = g`. Introduce `g hg`. Use `⟨sg σ.symm g, (hσ _).mp ?_, hinv g⟩` and prove the remaining obligations. Rewrite using `[hinv]`. Conclude with `hg`.

Establish `hAe` using `hcomm (sg σ) A hA hs1 hs2 v`. Establish `hev : e v = v` using `he.fix v hv`. Unfold `UpperTheory.Gal.LocD.jacA`. Use `Submodule.mem_map.mpr ⟨A v, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[← hev, hAe]`.

Conclude with `he.mem _`.
-/
theorem UpperTheory.Gal.Join.imStab :
    UpperTheory.Gal.Join.ImStab := by
  unfold UpperTheory.Gal.Join.ImStab UpperTheory.Gal.Join.ForRep
  intro k _ _ _ _ n V _ _ π hπ K hK
  have hH0 := heckeMul
  have hJ0 := jacNorm
  unfold UpperTheory.Gal.Join.HeckeMul UpperTheory.Gal.Join.ForRep at hH0
  unfold UpperTheory.Gal.Join.JacNorm UpperTheory.Gal.Join.ForRep at hJ0
  have hH := hH0 k n V π
  have hJ := hJ0 k n V π
  beta_reduce at hH hJ
  have hco := hK.co
  have hco' : IsCompact (K : Set (GL (Fin n) k)) ∧ IsOpen (K : Set (GL (Fin n) k)) := by
    unfold UpperTheory.ConvolutionTheory.C.CO at hco
    exact hco
  obtain ⟨e, he, hcomm⟩ := avgEx (GL (Fin n) k) V π hπ.1 K hco
  unfold UpperTheory.Gal.Join.imK
  haveI : FiniteDimensional ℂ (fixed π K) := hπ.2 K hco'.2 hco'.1
  haveI hfd : FiniteDimensional ℂ
      (Submodule.map (twKer π (unipB k (Fin n)) 1).mkQ (fixed π K)) :=
    Module.Finite.map _ _
  have hD : ∀ t : Fin n → kˣ, Dom t → ∀ y ∈ Submodule.map (twKer π (unipB k (Fin n)) 1).mkQ
      (fixed π K), jacBU π t y ∈ Submodule.map (twKer π (unipB k (Fin n)) 1).mkQ (fixed π K) := by
    intro t ht y hy
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hy
    rw [← (hH K hK e he t ht v hv).2]
    exact Submodule.mem_map_of_mem (he.mem _)
  have key : ∀ (s : Fin n → kˣ) (z : Jacquet π (unipB k (Fin n))),
      jacBU π s⁻¹ (jacBU π s z) = z := fun s z => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hU : ∀ t : Fin n → kˣ, ∀ y ∈ Submodule.map (twKer π (unipB k (Fin n)) 1).mkQ
      (fixed π K), jacBU π t y ∈ Submodule.map (twKer π (unipB k (Fin n)) 1).mkQ (fixed π K) := by
    intro t y hy
    obtain ⟨s, hs, hst⟩ := exists_dom t
    let f := (jacBU π s).restrict (fun z hz => hD s hs z hz)
    have hinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have h1 := congrArg (fun z => jacBU π s⁻¹ z) (congrArg Subtype.val hab)
      simpa [f, LinearMap.restrict_apply, key] using h1
    have hsurj := LinearMap.injective_iff_surjective.mp hinj
    obtain ⟨z, hz⟩ := hsurj ⟨_, hD _ hst y hy⟩
    have hz' : jacBU π s z = jacBU π (s * t) y := by
      have := congrArg Subtype.val hz
      simpa [f, LinearMap.restrict_apply] using this
    have h2 : jacBU π s (jacBU π t y) = jacBU π s z := by
      rw [hz', map_mul, Module.End.mul_apply]
    have h3 : jacBU π t y = z := by
      have := congrArg (fun w => jacBU π s⁻¹ w) h2
      simpa [key] using this
    rw [h3]
    exact z.2
  refine ⟨hfd, ?_, ?_⟩
  · intro t y hy
    have hpos : (0 : ℝ) < √(deltaB t) := Real.sqrt_pos.mpr (deltaB_pos t)
    have hne : ((√(deltaB t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have h1 : jacB π t y = (((√(deltaB t) : ℝ) : ℂ))⁻¹ • jacBU π t y := by
      rw [hJ t y, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [h1]
    exact Submodule.smul_mem _ _ (hU t y hy)
  · intro σ A hA hσ y hy
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hy
    have hinv : ∀ g : GL (Fin n) k, sg σ (sg σ.symm g) = g := by
      intro g
      ext i j
      rw [sg_val, sg_val, RingEquiv.apply_symm_apply]
    have hs1 : ∀ g ∈ K, sg σ g ∈ K := fun g hg => (hσ g).mpr hg
    have hs2 : ∀ g ∈ K, ∃ h ∈ K, sg σ h = g := by
      intro g hg
      refine ⟨sg σ.symm g, (hσ _).mp ?_, hinv g⟩
      rw [hinv]
      exact hg
    have hAe := hcomm (sg σ) A hA hs1 hs2 v
    have hev : e v = v := he.fix v hv
    unfold UpperTheory.Gal.LocD.jacA
    refine Submodule.mem_map.mpr ⟨A v, ?_, rfl⟩
    rw [← hev, hAe]
    exact he.mem _
