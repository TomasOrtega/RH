import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinNormalProjectiveModelExistsProof
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.SegreModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

/- English proof (translation)
Introduce `z` and use `by obtain ⟨i, h0, hi⟩ := h z refine ⟨i.1, left_ne_zero_of_mul h0, fun j => ?_⟩ have := hi (j, i.2) rwa [mul_div_mul_right _ _ (right_ne_zero_of_mul h0)] at this`.
-/
theorem hasDiv_left {A B : Type} {a : A → Ω} {b : B → Ω} (h : M.HasDiv fun p : A × B => a p.1 * b p.2) :
    M.HasDiv a := fun z => by
  obtain ⟨i, h0, hi⟩ := h z
  refine ⟨i.1, left_ne_zero_of_mul h0, fun j => ?_⟩
  have := hi (j, i.2)
  rwa [mul_div_mul_right _ _ (right_ne_zero_of_mul h0)] at this

/- English proof (translation)
Introduce `z` and use `by obtain ⟨i, h0, hi⟩ := h z refine ⟨i.2, right_ne_zero_of_mul h0, fun j => ?_⟩ have := hi (i.1, j) rwa [mul_div_mul_left _ _ (left_ne_zero_of_mul h0)] at this`.
-/
theorem hasDiv_right {A B : Type} {a : A → Ω} {b : B → Ω} (h : M.HasDiv fun p : A × B => a p.1 * b p.2) :
    M.HasDiv b := fun z => by
  obtain ⟨i, h0, hi⟩ := h z
  refine ⟨i.2, right_ne_zero_of_mul h0, fun j => ?_⟩
  have := hi (i.1, j)
  rwa [mul_div_mul_left _ _ (left_ne_zero_of_mul h0)] at this

/- English proof (translation)
Introduce `z` and use `by obtain ⟨i, h0, hi⟩ := h z have hne := Finset.prod_ne_zero_iff.1 h0 refine ⟨i k, hne k (Finset.mem_univ _), fun j => ?_⟩ have := hi (Function.update i k j) have e : ∏ l ∈ Finset.univ.erase k, t l (Function.update i k j l) = ∏ l ∈ Finset.univ.erase k, t l (i l) := Finset.prod_co …`.
-/
theorem hasDiv_of_prod {K : Type} [Fintype K] {J : K → Type} {t : ∀ k, J k → Ω}
    (h : M.HasDiv fun i : ∀ k, J k => ∏ k, t k (i k)) (k : K) : M.HasDiv (t k) := fun z => by
  obtain ⟨i, h0, hi⟩ := h z
  have hne := Finset.prod_ne_zero_iff.1 h0
  refine ⟨i k, hne k (Finset.mem_univ _), fun j => ?_⟩
  have := hi (Function.update i k j)
  have e : ∏ l ∈ Finset.univ.erase k, t l (Function.update i k j l) = ∏ l ∈ Finset.univ.erase k, t l (i l) :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have h1 : ∏ l ∈ Finset.univ.erase k, t l (i l) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => hne l (Finset.mem_univ _)
  simp only at this
  rwa [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ (fun l => t l (i l)) (Finset.mem_univ k),
    e, Function.update_self, mul_div_mul_right _ _ h1] at this

/- English proof (translation)
Take `⟨i, hi, -⟩` from `h.1 (genericPoint M.Z)`. Take `⟨U, hU, hD, hR⟩` from `h.2 i hi`. Establish `hne : (U : Set M.Z).Nonempty` using `⟨genericPoint M.Z, hD ▸ RatModel.div_genericPoint hi⟩`. Establish `hle : ∀ x ∈ M.ringOn U, x ∈ F`. Introduce `x hx`.

Rewrite `hx` using `[hR]`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem _ h' => obtain ⟨j, rfl⟩ := h'`. Conclude with `hc i j hi`. Consider the case `algebraMap r => exact ho ⟨r, rfl⟩`.

Consider the case `add a b _ _ ha hb => exact add_mem ha hb`. Consider the case `mul a b _ _ ha hb => exact mul_mem ha hb`. Use `top_unique fun x _ => ?_` and prove the remaining obligations. Take `⟨a, b, -, rfl⟩` from `RatModel.exists_eq_div hU hne x`. Conclude with `div_mem (hle _ ((RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩)) (hle _ ((RatModel.mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩))`.
-/
theorem subfield_eq_top {J : Type} {c : J → Ω} (h : M.IsCl c) (F : Subfield Ω)
    (ho : Set.range (algebraMap o Ω) ⊆ F) (hc : ∀ i j, c i ≠ 0 → c j / c i ∈ F) : F = ⊤ := by
  obtain ⟨i, hi, -⟩ := h.1 (genericPoint M.Z)
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi
  have hne : (U : Set M.Z).Nonempty := ⟨genericPoint M.Z, hD ▸ RatModel.div_genericPoint hi⟩
  have hle : ∀ x ∈ M.ringOn U, x ∈ F := by
    intro x hx
    rw [hR] at hx
    induction hx using Algebra.adjoin_induction with
    | mem _ h' => obtain ⟨j, rfl⟩ := h'; exact hc i j hi
    | algebraMap r => exact ho ⟨r, rfl⟩
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  refine top_unique fun x _ => ?_
  obtain ⟨a, b, -, rfl⟩ := RatModel.exists_eq_div hU hne x
  exact div_mem (hle _ ((RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩))
    (hle _ ((RatModel.mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩))

/- English proof (translation)
The claim follows from `Module.Finite.of_surjective (Algebra.linearMap F Ω) fun x => ⟨⟨x, h ▸ trivial⟩, rfl⟩`.
-/
theorem finite_of_eq_top (F : Subfield Ω) (h : F = ⊤) : Module.Finite F Ω :=
  Module.Finite.of_surjective (Algebra.linearMap F Ω) fun x => ⟨⟨x, h ▸ trivial⟩, rfl⟩

end GlobalTheory.Poinc.SegreModel

/- English proof (translation)
Introduce `o Ω _ _ _ _ S ρ hBig M₁ hM₁ K _ Jk _ t ht`. Take `⟨n, c, hc⟩` from `RatModel.exists_isCl_of_isProjOver hM₁`. Establish `hN2` using `S.N_ge`. Use `haveI hN0 : NeZero S.N := ⟨by omega⟩`. Use `haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by omega)⟩`.

Use `haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩`. Use `haveI : Finite (AddSubgroup S.Gam) := Finite.of_injective (fun H : AddSubgroup S.Gam => (H : Set S.Gam)) SetLike.coe_injective`. Use `haveI : ∀ T₀ : AddSubgroup S.Gam, Finite (T₀ →+ ZMod S.N) := fun T₀ => Finite.of_injective (fun f : T₀ →+ ZMod S.N => (f : T₀ → ZMod S.N)) DFunLike.coe_injective`. Set `K₁` to `{k : K // Nonempty (Jk k)}`. Set `K₂` to `{d : Σ T : AddSubgroup S.Gam, (T →+ ZMod S.N) // S.FF d.1 d.2 ≠ 0}`.

Use `letI : Fintype K₁ := Fintype.ofFinite _`. Use `letI : Fintype K₂ := Fintype.ofFinite _`. Set `J₂ : K₂ → Type` to `fun d => S.J × (d.1.1 → ZMod ((S.r * S.N) ^ 2))`. Set `B` to `(∀ k : K₁, Jk k.1) × (∀ d : K₂, J₂ d)`. Set `b : B → Ω` to `fun p => (∏ k : K₁, t k.1 (p.1 k)) * ∏ d : K₂, S.FF d.1.1 d.1.2 (p.2 d)`.

Use `haveI : Finite B := inferInstance`. Use `letI : Fintype (Fin (n + 1) × B) := Fintype.ofFinite _`. Take `⟨p₀, hp₀⟩ : ∃ p, b p ≠ 0` from `by choose κ hκ using fun d : K₂ => Function.ne_iff.1 d.2`. Conclude with `⟨(fun k => k.2.some, κ), mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => ht _ _) (Finset.prod_ne_zero_iff.2 fun d _ => hκ d)⟩`. Take `⟨i₀, hi₀, -⟩` from `hc.1 (genericPoint M₁.Z)`.

Take `⟨x₀, hx₀⟩` from `S.th_ne`. Take `⟨Y, U₀, EE, hO, hD, hE, ⟨FinalForm⟩⟩` from `GlobalTheory.zhSt_holds o Ω S ρ hBig (Fin (n + 1) × B) (fun p => c p.1 * b p.2) ⟨(i₀, p₀), mul_ne_zero hi₀ hp₀⟩ (by`. Use `SegreModel.finite_of_eq_top _ (SegreModel.subfield_eq_top hc _ (Set.subset_union_left.trans Subfield.subset_closure) fun i j _ => Subfield.subset_closure (Or.inr ⟨(x₀, i, p₀), (x₀, j, p₀), ?_⟩))` and prove the remaining obligations. Rewrite using `[mul_div_mul_left _ _ hx₀, mul_div_mul_right _ _ hp₀])`. Establish `hb : Y.HasDiv b` using `SegreModel.hasDiv_right hD`.

Establish `h1` using `SegreModel.hasDiv_left (a := fun q : ∀ k : K₁, Jk k.1 => ∏ k : K₁, t k.1 (q k)) (b := fun q : ∀ d : K₂, J₂ d => ∏ d : K₂, S.FF d.1.1 d.1.2 (q d)) hb`. Establish `h2` using `SegreModel.hasDiv_right (a := fun q : ∀ k : K₁, Jk k.1 => ∏ k : K₁, t k.1 (q k)) (b := fun q : ∀ d : K₂, J₂ d => ∏ d : K₂, S.FF d.1.1 d.1.2 (q d)) hb`. Take `⟨π, hπ⟩` from `hc.exists_isHom (M' := Y) (φ := AlgHom.id o Ω) (SegreModel.hasDiv_left hD)`. Use `⟨Y, π, U₀, EE, FinalForm, hπ, ?_, ⟨hO, fun T c' _ h => ?_⟩, hE, fun k hk => ?_⟩` and prove the remaining obligations. Use `haveI := M₁.sep haveI : IsProper (π ≫ M₁.s) := by`.

Rewrite using `[hπ.inducedModelMorphism_comp_structureMap]`. Take `⟨m, j, hj, hs⟩` from `hO.proj`. Rewrite using `[← hs]`. Use `isProper_str o m` as an intermediate fact. Use `infer_instance`.

Conclude with `IsProper.of_comp π M₁.s`. Conclude with `SegreModel.hasDiv_of_prod (t := fun d : K₂ => S.FF d.1.1 d.1.2) h2 ⟨⟨T, c'⟩, h⟩`. Conclude with `SegreModel.hasDiv_of_prod (t := fun k : K₁ => t k.1) h1 ⟨k, hk⟩`.
-/
theorem GlobalTheory.Poinc.exists_admissible_projective_theta_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → ∀ M₁ : RatModel o Ω, IsProjOver M₁.s → ∀ (K : Type) [Finite K] (Jk : K → Type) [∀ k, Finite (Jk k)] (t : ∀ k, Jk k → Ω), (∀ k j, t k j ≠ 0) → ∃ (Y : RatModel o Ω) (πY : Y.Z ⟶ M₁.Z) (U₀ : Y.Z.Opens) (EE : Y.Lat S.J) (_ : ZHOut ρ Y U₀ EE), M₁.IsHom Y (AlgHom.id o Ω) πY ∧ IsProper πY ∧ S.admitted Y U₀ ∧ S.IsEE Y U₀ EE ∧ ∀ k, Nonempty (Jk k) → Y.HasDiv (t k) := by
  intro o Ω _ _ _ _ S ρ hBig M₁ hM₁ K _ Jk _ t ht
  obtain ⟨n, c, hc⟩ := RatModel.exists_isCl_of_isProjOver hM₁
  have hN2 := S.N_ge
  haveI hN0 : NeZero S.N := ⟨by omega⟩
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by omega)⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  haveI : Finite (AddSubgroup S.Gam) :=
    Finite.of_injective (fun H : AddSubgroup S.Gam => (H : Set S.Gam)) SetLike.coe_injective
  haveI : ∀ T₀ : AddSubgroup S.Gam, Finite (T₀ →+ ZMod S.N) := fun T₀ =>
    Finite.of_injective (fun f : T₀ →+ ZMod S.N => (f : T₀ → ZMod S.N)) DFunLike.coe_injective
  let K₁ := {k : K // Nonempty (Jk k)}
  let K₂ := {d : Σ T : AddSubgroup S.Gam, (T →+ ZMod S.N) // S.FF d.1 d.2 ≠ 0}
  letI : Fintype K₁ := Fintype.ofFinite _
  letI : Fintype K₂ := Fintype.ofFinite _
  let J₂ : K₂ → Type := fun d => S.J × (d.1.1 → ZMod ((S.r * S.N) ^ 2))
  let B := (∀ k : K₁, Jk k.1) × (∀ d : K₂, J₂ d)
  let b : B → Ω := fun p => (∏ k : K₁, t k.1 (p.1 k)) * ∏ d : K₂, S.FF d.1.1 d.1.2 (p.2 d)
  haveI : Finite B := inferInstance
  letI : Fintype (Fin (n + 1) × B) := Fintype.ofFinite _
  obtain ⟨p₀, hp₀⟩ : ∃ p, b p ≠ 0 := by
    choose κ hκ using fun d : K₂ => Function.ne_iff.1 d.2
    exact ⟨(fun k => k.2.some, κ), mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => ht _ _)
      (Finset.prod_ne_zero_iff.2 fun d _ => hκ d)⟩
  obtain ⟨i₀, hi₀, -⟩ := hc.1 (genericPoint M₁.Z)
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  obtain ⟨Y, U₀, EE, hO, hD, hE, ⟨FinalForm⟩⟩ := GlobalTheory.zhSt_holds o Ω S ρ hBig (Fin (n + 1) × B) (fun p => c p.1 * b p.2)
    ⟨(i₀, p₀), mul_ne_zero hi₀ hp₀⟩ (by
      refine SegreModel.finite_of_eq_top _ (SegreModel.subfield_eq_top hc _
        (Set.subset_union_left.trans Subfield.subset_closure) fun i j _ =>
        Subfield.subset_closure (Or.inr ⟨(x₀, i, p₀), (x₀, j, p₀), ?_⟩))
      rw [mul_div_mul_left _ _ hx₀, mul_div_mul_right _ _ hp₀])
  have hb : Y.HasDiv b := SegreModel.hasDiv_right hD
  have h1 := SegreModel.hasDiv_left (a := fun q : ∀ k : K₁, Jk k.1 => ∏ k : K₁, t k.1 (q k))
    (b := fun q : ∀ d : K₂, J₂ d => ∏ d : K₂, S.FF d.1.1 d.1.2 (q d)) hb
  have h2 := SegreModel.hasDiv_right (a := fun q : ∀ k : K₁, Jk k.1 => ∏ k : K₁, t k.1 (q k))
    (b := fun q : ∀ d : K₂, J₂ d => ∏ d : K₂, S.FF d.1.1 d.1.2 (q d)) hb
  obtain ⟨π, hπ⟩ := hc.exists_isHom (M' := Y) (φ := AlgHom.id o Ω) (SegreModel.hasDiv_left hD)
  refine ⟨Y, π, U₀, EE, FinalForm, hπ, ?_, ⟨hO, fun T c' _ h => ?_⟩, hE, fun k hk => ?_⟩
  · haveI := M₁.sep
    haveI : IsProper (π ≫ M₁.s) := by
      rw [hπ.inducedModelMorphism_comp_structureMap]
      obtain ⟨m, j, hj, hs⟩ := hO.proj
      rw [← hs]
      have := isProper_str o m
      infer_instance
    exact IsProper.of_comp π M₁.s
  · exact SegreModel.hasDiv_of_prod (t := fun d : K₂ => S.FF d.1.1 d.1.2) h2 ⟨⟨T, c'⟩, h⟩
  · exact SegreModel.hasDiv_of_prod (t := fun k : K₁ => t k.1) h1 ⟨k, hk⟩
