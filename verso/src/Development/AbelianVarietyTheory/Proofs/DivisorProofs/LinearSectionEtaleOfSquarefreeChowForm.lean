import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqIsoSpecComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPtOfMemConeOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormZeroSetExtensionFieldIffCommonConeZeroStatement

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
open GlobalTheory.HSChoice.EtaleSection

namespace GlobalTheory.HSShort.EtaleSection

/- English proof (translation)
Rewrite using `[eval_spec]`. Take `⟨hA, hB⟩` from `GlobalTheory.T.chowForm_zeroSet_extensionField_iff_common_cone_zero F _ _ δ _ f hf`. Establish `hs : ∀ (u y : Fin T.N → AlgebraicClosure E) (c : AlgebraicClosure E), ∑ j, u j * y j = 0 → ∑ j, u j * (c • y) j = 0` using `fun u y c h => by`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum]`. Rewrite using `[h, mul_zero]`.

Prove the components needed by the constructor for the conclusion. Introduce `h0`. Take `⟨y, hy, hc, h₁, h₂⟩` from `hB _ _ _ h0`. Take `⟨x₀, c, -, h⟩` from `GlobalTheory.ConeOnto.exists_pt_of_mem_cone_of_isAlgClosed F T.toLinSys hT.alg.variety hT.alg.bpf _ y hy hc`. Take `⟨x, rfl⟩` from `(T.toLinSys.toBase_bijective E (AlgebraicClosure E)).2 x₀`.

Apply the tactic sequence `refine ⟨x, (T.toLinSys.mem_subPts_cut_baseChange_iff E s x).2 fun i => ?_, ?_⟩ <;> rw [h]`. Conclude with `hs _ _ _ (h₁ i)`. Conclude with `hs _ _ _ h₂`. Introduce and unpack `⟨x, hx, h⟩`. Use `hA _ _ _ _ (hT.alg.bpf.coords_ne_zero _) (fun g hg => ?_) ((T.toLinSys.mem_subPts_cut_baseChange_iff E s x).1 hx) h` and prove the remaining obligations.

Use `T.toLinSys.eval₂_coords_eq_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 hg` as an intermediate fact. Rewrite `this` using `[LinSys.baseHom_ptOver]`. Then use the resulting hypothesis.
-/
theorem spec_zero_iff {F : Type} [Field F] [NumberField F] (T : Tuple F) (hT : T.IsGeometric) (δ : ℕ)
    (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F) (hf : IsChowForm T.imageIdeal T.D δ f)
    (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E) (ξ : Fin T.N → AlgebraicClosure E) :
    eval (fun p => ξ p.2) (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) = 0 ↔
      ∃ x ∈ T.geomPts E (T.linSection E s),
        ∑ j, ξ j * T.coords (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 j = 0 := by
  rw [eval_spec]
  obtain ⟨hA, hB⟩ := GlobalTheory.T.chowForm_zeroSet_extensionField_iff_common_cone_zero F _ _ δ _ f hf
  have hs : ∀ (u y : Fin T.N → AlgebraicClosure E) (c : AlgebraicClosure E), ∑ j, u j * y j = 0 →
      ∑ j, u j * (c • y) j = 0 := fun u y c h => by
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum]
    rw [h, mul_zero]
  constructor
  · intro h0
    obtain ⟨y, hy, hc, h₁, h₂⟩ := hB _ _ _ h0
    obtain ⟨x₀, c, -, h⟩ := GlobalTheory.ConeOnto.exists_pt_of_mem_cone_of_isAlgClosed F T.toLinSys hT.alg.variety hT.alg.bpf _ y hy hc
    obtain ⟨x, rfl⟩ := (T.toLinSys.toBase_bijective E (AlgebraicClosure E)).2 x₀
    refine ⟨x, (T.toLinSys.mem_subPts_cut_baseChange_iff E s x).2 fun i => ?_, ?_⟩ <;> rw [h]
    · exact hs _ _ _ (h₁ i)
    · exact hs _ _ _ h₂
  · rintro ⟨x, hx, h⟩
    refine hA _ _ _ _ (hT.alg.bpf.coords_ne_zero _) (fun g hg => ?_)
      ((T.toLinSys.mem_subPts_cut_baseChange_iff E s x).1 hx) h
    have := T.toLinSys.eval₂_coords_eq_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 hg
    rwa [LinSys.baseHom_ptOver] at this

/- English proof (translation)
Introduce `F _ _ T hT δ f hf hδ E _ _ s hfin hopen hsq`. Take `⟨hfs, hmod, hrank⟩` from `finite_finrank T hT E s hfin`. Use `letI := algebraΓOfHom ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)`. Use `haveI := hmod`. Establish `hPfin : (T.geomPts E (T.linSection E s)).Finite` using `hfs.finite_subPts _`.

Establish `hcard` using `natCard_subPts _ _ hfs (AlgebraicClosure E)`. Establish `hI` using `GlobalTheory.T.etale_of_finrank_le_card_algHom E Γ((T.linSection E s).subscheme, ⊤)`. Use `set P := T.geomPts E (T.linSection E s) with hPdef`. Use `set Ω := AlgebraicClosure E`. Set `yv : (T.toLinSys.baseChange E).Pt Ω → Fin T.N → Ω` to `fun x => T.coords (LinSys.toBase x : T.Pt Ω).1`.

Establish `hyv : ∀ x, yv x ≠ 0` using `fun x => hT.alg.bpf.coords_ne_zero _`. Set `line : (T.toLinSys.baseChange E).Pt Ω → Submodule Ω (Fin T.N → Ω)` to `fun x => Submodule.span Ω {yv x}`. Establish `: Finite (line '' P)` using `(hPfin.image line).to_subtype`. Set `eR : (line '' P) ≃ Fin (Nat.card (line '' P))` to `Finite.equivFin _`. Establish `hrep : ∀ q : Fin (Nat.card (line '' P)), ∃ x ∈ P, line x = (eR.symm q : Submodule Ω (Fin T.N → Ω))` using `fun q => (eR.symm q).2`.

Use `choose rep hrepP hrepl using hrep`. Set `y : Fin (Nat.card (line '' P)) → Fin T.N → Ω` to `fun q => yv (rep q)`. Establish `hinj : ∀ q q', line (rep q) = line (rep q') → q = q'`. Introduce `q q' h`. Apply `eR.symm.injective` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hrepl, ← hrepl, h]`. Establish `hzero : ∀ ξ : Fin T.N → Ω, eval (fun p => ξ p.2) (spec (fun i j => algebraMap E Ω (s i j)) f) = 0 ↔ ∃ q, ∑ j, ξ j * y q j = 0`. Introduce `ξ`. Rewrite using `[spec_zero_iff T hT δ f hf E s ξ]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, h0⟩`. Take `⟨q0, hq0⟩ : ∃ q0, eR.symm q0 = ⟨line x, x, hx, rfl⟩` from `⟨_, eR.symm_apply_apply _⟩`. Use `⟨q0, ?_⟩` and prove the remaining obligations. Establish `hl : line (rep q0) = line x` using `by rw [hrepl, hq0]`.

Establish `hm : y q0 ∈ line x`. Rewrite using `[← hl]`. Conclude with `Submodule.mem_span_singleton_self _`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.1 hm`. Rewrite using `[← ha]`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ a, ← Finset.mul_sum]`. Rewrite using `[h0, mul_zero]`. Introduce and unpack `⟨q, hq⟩`. Conclude with `⟨rep q, hrepP q, hq⟩`. Establish `hprop : ∀ q q' (c : Ω), y q' = c • y q → q = q'`.

Introduce `q q' c h`. Establish `hc : c ≠ 0`. Introduce and unpack `rfl`. Conclude with `hyv _ (by simpa using h)`. Apply `hinj` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `Submodule.span Ω {yv (rep q)} = Submodule.span Ω {yv (rep q')}`. Rewrite using `[show yv (rep q') = c • yv (rep q) from h, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]`. Take `⟨hmδ, c, hc, hfac⟩` from `HyperplaneFactor.eq_C_mul_prod_lin Ω T.N δ _ _ y (isHomogeneous_spec _ f hf.homog) hsq (fun q => hyv _) hprop hzero`. Establish `hPf : Finite P` using `hPfin.to_subtype`. Establish `hrepinj : Function.Injective (fun q => (⟨rep q, hrepP q⟩ : P))` using `fun q q' h => hinj q q' (by rw [show rep q = rep q' from congrArg Subtype.val h])`.

Establish `hfr : (Module.finrank E Γ((T.linSection E s).subscheme, ⊤) : ℤ) = δ` using `hrank.trans hδ.symm`. Establish `h1 : Nat.card P = Nat.card (Γ((T.linSection E s).subscheme, ⊤) →ₐ[E] AlgebraicClosure E)` using `hcard`. Establish `h3 : Module.finrank E Γ((T.linSection E s).subscheme, ⊤) = δ` using `by exact_mod_cast hfr`. Establish `hPle : Nat.card P ≤ δ`. Establish `h2` using `hI.2.1`.

Use linear arithmetic over natural numbers and integers. Establish `hmP : Nat.card (Fin (Nat.card (line '' P))) ≤ Nat.card P` using `Nat.card_le_card_of_injective _ hrepinj`. Rewrite `hmP` using `[Nat.card_fin]`. Establish `hPδ : Nat.card P = δ` using `by omega`. Establish `hbij : Function.Bijective (fun q => (⟨rep q, hrepP q⟩ : P))` using `hrepinj.bijective_of_nat_card_le (by rw [Nat.card_fin]; show Nat.card P ≤ _; omega)`.

Use `⟨⟨⟨hfs, etale_of_algebraEtale _ _ hfs (hI.2.2 ?_)⟩, hopen⟩, ?_, ?_, c, hc, ?_⟩` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers. Rewrite using `[← Nat.card_coe_set_eq]`. Conclude with `hPδ`. Introduce `x hx x' hx' a ha h`.

Take `⟨q, hq⟩` from `hbij.2 ⟨x, hx⟩`. Take `⟨q', hq'⟩` from `hbij.2 ⟨x', hx'⟩`. Take `rfl : rep q = x` from `congrArg Subtype.val hq`. Take `rfl : rep q' = x'` from `congrArg Subtype.val hq'`. Take `⟨b, hb, e⟩` from `T.toLinSys.exists_coords_baseChange E (rep q).1`.

Take `⟨b', hb', e'⟩` from `T.toLinSys.exists_coords_baseChange E (rep q').1`. Establish `e₁ : b' • y q' = a • b • y q` using `e'.symm.trans (h.trans (congrArg (a • ·) e))`. Rewrite using `[hprop q q' (b'⁻¹ * a * b) (by rw [mul_smul, mul_smul, ← e₁, inv_smul_smul₀ hb'])]`. Rewrite using `[hfac]`. Use `congr 1`.

Rewrite using `[← finprod_eq_prod_of_fintype, ← finprod_mem_univ]`. Use `finprod_mem_eq_of_bijOn rep ⟨fun q _ => hrepP q, fun q _ q' _ h => hinj q q' (by rw [h]), fun x hx => ?_⟩ fun q _ => rfl` and prove the remaining obligations. Take `⟨q, hq⟩` from `hbij.2 ⟨x, hx⟩`. Conclude with `⟨q, Set.mem_univ _, congrArg Subtype.val hq⟩`.
-/
theorem simpleAt_of_noSquare : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f → (δ : ℤ) = T.del → ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E), ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite → T.InOpen E (T.linSection E s) → NoSquare (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) → SimpleAt T δ f E s := by
  intro F _ _ T hT δ f hf hδ E _ _ s hfin hopen hsq
  classical
  obtain ⟨hfs, hmod, hrank⟩ := finite_finrank T hT E s hfin
  letI := algebraΓOfHom ((T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str)
  haveI := hmod
  have hPfin : (T.geomPts E (T.linSection E s)).Finite := hfs.finite_subPts _
  have hcard := natCard_subPts _ _ hfs (AlgebraicClosure E)
  have hI := GlobalTheory.T.etale_of_finrank_le_card_algHom E Γ((T.linSection E s).subscheme, ⊤)
  set P := T.geomPts E (T.linSection E s) with hPdef
  set Ω := AlgebraicClosure E
  let yv : (T.toLinSys.baseChange E).Pt Ω → Fin T.N → Ω := fun x => T.coords (LinSys.toBase x : T.Pt Ω).1
  have hyv : ∀ x, yv x ≠ 0 := fun x => hT.alg.bpf.coords_ne_zero _
  let line : (T.toLinSys.baseChange E).Pt Ω → Submodule Ω (Fin T.N → Ω) := fun x => Submodule.span Ω {yv x}
  have : Finite (line '' P) := (hPfin.image line).to_subtype
  let eR : (line '' P) ≃ Fin (Nat.card (line '' P)) := Finite.equivFin _
  have hrep : ∀ q : Fin (Nat.card (line '' P)), ∃ x ∈ P, line x = (eR.symm q : Submodule Ω (Fin T.N → Ω)) :=
    fun q => (eR.symm q).2
  choose rep hrepP hrepl using hrep
  let y : Fin (Nat.card (line '' P)) → Fin T.N → Ω := fun q => yv (rep q)
  have hinj : ∀ q q', line (rep q) = line (rep q') → q = q' := by
    intro q q' h
    apply eR.symm.injective
    apply Subtype.ext
    rw [← hrepl, ← hrepl, h]
  have hzero : ∀ ξ : Fin T.N → Ω, eval (fun p => ξ p.2) (spec (fun i j => algebraMap E Ω (s i j)) f) = 0 ↔
      ∃ q, ∑ j, ξ j * y q j = 0 := by
    intro ξ
    rw [spec_zero_iff T hT δ f hf E s ξ]
    constructor
    · rintro ⟨x, hx, h0⟩
      obtain ⟨q0, hq0⟩ : ∃ q0, eR.symm q0 = ⟨line x, x, hx, rfl⟩ := ⟨_, eR.symm_apply_apply _⟩
      refine ⟨q0, ?_⟩
      have hl : line (rep q0) = line x := by rw [hrepl, hq0]
      have hm : y q0 ∈ line x := by
        rw [← hl]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hm
      rw [← ha]
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ a, ← Finset.mul_sum]
      rw [h0, mul_zero]
    · rintro ⟨q, hq⟩
      exact ⟨rep q, hrepP q, hq⟩
  have hprop : ∀ q q' (c : Ω), y q' = c • y q → q = q' := by
    intro q q' c h
    have hc : c ≠ 0 := by
      rintro rfl
      exact hyv _ (by simpa using h)
    apply hinj
    change Submodule.span Ω {yv (rep q)} = Submodule.span Ω {yv (rep q')}
    rw [show yv (rep q') = c • yv (rep q) from h, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]
  obtain ⟨hmδ, c, hc, hfac⟩ := HyperplaneFactor.eq_C_mul_prod_lin Ω T.N δ _ _ y
    (isHomogeneous_spec _ f hf.homog) hsq (fun q => hyv _) hprop hzero
  have hPf : Finite P := hPfin.to_subtype
  have hrepinj : Function.Injective (fun q => (⟨rep q, hrepP q⟩ : P)) := fun q q' h =>
    hinj q q' (by rw [show rep q = rep q' from congrArg Subtype.val h])
  have hfr : (Module.finrank E Γ((T.linSection E s).subscheme, ⊤) : ℤ) = δ := hrank.trans hδ.symm
  have h1 : Nat.card P = Nat.card (Γ((T.linSection E s).subscheme, ⊤) →ₐ[E] AlgebraicClosure E) := hcard
  have h3 : Module.finrank E Γ((T.linSection E s).subscheme, ⊤) = δ := by exact_mod_cast hfr
  have hPle : Nat.card P ≤ δ := by
    have h2 := hI.2.1
    omega
  have hmP : Nat.card (Fin (Nat.card (line '' P))) ≤ Nat.card P := Nat.card_le_card_of_injective _ hrepinj
  rw [Nat.card_fin] at hmP
  have hPδ : Nat.card P = δ := by omega
  have hbij : Function.Bijective (fun q => (⟨rep q, hrepP q⟩ : P)) :=
    hrepinj.bijective_of_nat_card_le (by rw [Nat.card_fin]; show Nat.card P ≤ _; omega)
  refine ⟨⟨⟨hfs, etale_of_algebraEtale _ _ hfs (hI.2.2 ?_)⟩, hopen⟩, ?_, ?_, c, hc, ?_⟩
  · omega
  · rw [← Nat.card_coe_set_eq]
    exact hPδ
  · intro x hx x' hx' a ha h
    obtain ⟨q, hq⟩ := hbij.2 ⟨x, hx⟩
    obtain ⟨q', hq'⟩ := hbij.2 ⟨x', hx'⟩
    obtain rfl : rep q = x := congrArg Subtype.val hq
    obtain rfl : rep q' = x' := congrArg Subtype.val hq'
    obtain ⟨b, hb, e⟩ := T.toLinSys.exists_coords_baseChange E (rep q).1
    obtain ⟨b', hb', e'⟩ := T.toLinSys.exists_coords_baseChange E (rep q').1
    have e₁ : b' • y q' = a • b • y q := e'.symm.trans (h.trans (congrArg (a • ·) e))
    rw [hprop q q' (b'⁻¹ * a * b) (by rw [mul_smul, mul_smul, ← e₁, inv_smul_smul₀ hb'])]
  · rw [hfac]
    congr 1
    rw [← finprod_eq_prod_of_fintype, ← finprod_mem_univ]
    refine finprod_mem_eq_of_bijOn rep ⟨fun q _ => hrepP q, fun q _ q' _ h => hinj q q' (by rw [h]), fun x hx => ?_⟩
      fun q _ => rfl
    obtain ⟨q, hq⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨q, Set.mem_univ _, congrArg Subtype.val hq⟩

end GlobalTheory.HSShort.EtaleSection
