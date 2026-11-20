import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.JetDim

/- English proof (translation)
Use `haveI : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K`. Set `iB : F →+* B` to `(φ.comp (algebraMap F K)).codRestrict B hF`. Use `letI : Algebra F B := iB.toAlgebra`. Use `letI : Algebra F R := (φ.comp (algebraMap F K)).toAlgebra`. Set `I : Ideal B` to `N.comap B.subtype`.

Establish `hI : IsNilpotent I`. Take `⟨n, hn⟩` from `hN`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h1 : I ^ n ≤ (N ^ n).comap B.subtype` using `Ideal.le_comap_pow _ n`. Rewrite using `[Ideal.zero_eq_bot, eq_bot_iff]`.

Introduce `x hx`. Use `h1 hx` as an intermediate fact. Rewrite `this` using `[hn, Ideal.zero_eq_bot, Ideal.mem_comap, Ideal.mem_bot]`. Rewrite using `[Ideal.mem_bot]`. Conclude with `Subtype.ext this`.

Set `g : K →ₐ[F] B ⧸ I` to `{ toRingHom := (Ideal.Quotient.mk I).comp σ commutes' := fun c => by`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I (σ (algebraMap F K c)) = Ideal.Quotient.mk I (iB c)`. Rewrite using `[Ideal.Quotient.eq, Ideal.mem_comap, map_sub]`. Use `N.neg_mem (hσ (algebraMap F K c))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `[iB] }`. Set `ψ : K →ₐ[F] B` to `Algebra.FormallySmooth.lift I hI g`. Set `ψR : K →ₐ[F] R` to `{ toRingHom := B.subtype.comp ψ.toRingHom commutes' := fun c => by`. Express the relevant statement in the definitionally equal form `B.subtype (ψ (algebraMap F K c)) = φ (algebraMap F K c)`. Rewrite using `[ψ.commutes]`.

Use `rfl }`. Set `φF : K →ₐ[F] R` to `{ toRingHom := φ, commutes' := fun c => rfl }`. Establish `e : ψR = φF`. Use `Algebra.FormallyUnramified.ext N hN (fun x => ?_)` and prove the remaining obligations. Establish `h1` using `Algebra.FormallySmooth.mk_lift I hI g x`.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I (ψ x) = Ideal.Quotient.mk I (σ x) at h1`. Rewrite `h1` using `[Ideal.Quotient.eq, Ideal.mem_comap, map_sub]`. Rewrite using `[Ideal.Quotient.eq]`. Use `N.sub_mem h1 (hσ x)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Express the relevant statement in the definitionally equal form `(ψ x : R) - φ x = _`. Simplify using `only [Subring.coe_subtype]`. Expand and normalize the polynomial expressions, which then agree. Use `DFunLike.congr_fun e a` as an intermediate fact. Express the relevant statement in the definitionally equal form `(ψ a : R) = φ a at this`.

Rewrite using `[← this]`. Conclude with `(ψ a).2`.
-/
theorem mem_of_formallyEtale {K R F : Type} [Field K] [CommRing R] [Field F] [Algebra F K]
    [Algebra.IsSeparable F K] (φ : K →+* R) (B : Subring R)
    (hF : ∀ c : F, φ (algebraMap F K c) ∈ B) (N : Ideal R) (hN : IsNilpotent N)
    (σ : K →+* B) (hσ : ∀ a, φ a - σ a ∈ N) (a : K) : φ a ∈ B := by
  haveI : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  let iB : F →+* B := (φ.comp (algebraMap F K)).codRestrict B hF
  letI : Algebra F B := iB.toAlgebra
  letI : Algebra F R := (φ.comp (algebraMap F K)).toAlgebra
  let I : Ideal B := N.comap B.subtype
  have hI : IsNilpotent I := by
    obtain ⟨n, hn⟩ := hN
    refine ⟨n, ?_⟩
    have h1 : I ^ n ≤ (N ^ n).comap B.subtype := Ideal.le_comap_pow _ n
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    intro x hx
    have := h1 hx
    rw [hn, Ideal.zero_eq_bot, Ideal.mem_comap, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    exact Subtype.ext this
  let g : K →ₐ[F] B ⧸ I :=
    { toRingHom := (Ideal.Quotient.mk I).comp σ
      commutes' := fun c => by
        change Ideal.Quotient.mk I (σ (algebraMap F K c)) = Ideal.Quotient.mk I (iB c)
        rw [Ideal.Quotient.eq, Ideal.mem_comap, map_sub]
        have := N.neg_mem (hσ (algebraMap F K c))
        convert this using 1
        simp [iB] }
  let ψ : K →ₐ[F] B := Algebra.FormallySmooth.lift I hI g
  let ψR : K →ₐ[F] R :=
    { toRingHom := B.subtype.comp ψ.toRingHom
      commutes' := fun c => by
        change B.subtype (ψ (algebraMap F K c)) = φ (algebraMap F K c)
        rw [ψ.commutes]
        rfl }
  let φF : K →ₐ[F] R := { toRingHom := φ, commutes' := fun c => rfl }
  have e : ψR = φF := by
    refine Algebra.FormallyUnramified.ext N hN (fun x => ?_)
    have h1 := Algebra.FormallySmooth.mk_lift I hI g x
    change Ideal.Quotient.mk I (ψ x) = Ideal.Quotient.mk I (σ x) at h1
    rw [Ideal.Quotient.eq, Ideal.mem_comap, map_sub] at h1
    rw [Ideal.Quotient.eq]
    have := N.sub_mem h1 (hσ x)
    convert this using 1
    change (ψ x : R) - φ x = _
    simp only [Subring.coe_subtype]
    ring
  have := DFunLike.congr_fun e a
  change (ψ a : R) = φ a at this
  rw [← this]
  exact (ψ a).2

end GlobalTheory.JetDim

namespace GlobalTheory.JetDim

/- English proof (translation)
Introduce `κ κ' _ _ _ _ k M ρ hz0`. Use `letI : Algebra κ' (κ ⊗[ℂ] κ') := Algebra.TensorProduct.rightAlgebra`. Take `⟨z, hz⟩` from `hz0`. Use `set J := RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) with hJ`. Break down `Nat.eq_zero_or_pos M with rfl | hM` into its components or cases.

Use `haveI : Subsingleton ((κ ⊗[ℂ] κ') ⧸ J ^ 0) := Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top])`. Conclude with `⟨by rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _, inferInstance⟩`. Set `mk : κ ⊗[ℂ] κ' →+* (κ ⊗[ℂ] κ') ⧸ J ^ M` to `Ideal.Quotient.mk (J ^ M)`. Set `φ : κ →+* (κ ⊗[ℂ] κ') ⧸ J ^ M` to `mk.comp Algebra.TensorProduct.includeLeftRingHom`. Set `N : Ideal ((κ ⊗[ℂ] κ') ⧸ J ^ M)` to `J.map mk`.

Establish `hNM : N ^ M = ⊥` using `by rw [← Ideal.map_pow, Ideal.map_quotient_self]`. Establish `hN : IsNilpotent N` using `⟨M, by rw [Ideal.zero_eq_bot]; exact hNM⟩`. Establish `hφσ : ∀ a, φ a - algebraMap κ' _ (ρ a) ∈ N`. Introduce `a`. Establish `e : φ a - algebraMap κ' _ (ρ a) = mk (a ⊗ₜ 1 - 1 ⊗ₜ ρ a)` using `by rw [map_sub]; rfl`.

Rewrite using `[e]`. Use `Ideal.mem_map_of_mem _ ?_` and prove the remaining obligations. Simplify using `[hJ, RingHom.mem_ker, Algebra.TensorProduct.productMap_apply_tmul]`. Set `t : Fin k → (κ ⊗[ℂ] κ') ⧸ J ^ M` to `fun i => φ (z i) - algebraMap κ' _ (ρ (z i))`. Set `B : Subalgebra κ' ((κ ⊗[ℂ] κ') ⧸ J ^ M)` to `Algebra.adjoin κ' (Set.range t)`.

Establish `hzB : ∀ i, φ (z i) ∈ B`. Introduce `i`. Establish `: φ (z i) = t i + algebraMap κ' _ (ρ (z i))` using `by simp [t]`. Rewrite using `[this]`. Conclude with `B.add_mem (Algebra.subset_adjoin ⟨i, rfl⟩) (B.algebraMap_mem _)`.

Set `F : IntermediateField ℂ κ` to `{ carrier := {a | φ a ∈ B} mul_mem' := fun {a b} ha hb => by show φ (a * b) ∈ B`. Rewrite using `[map_mul]`. Conclude with `B.mul_mem ha hb`. Use the proof step `one_mem' := by show φ 1 ∈ B; rw [map_one]; exact B.one_mem`. Use the proof step `add_mem' := fun {a b} ha hb => by show φ (a + b) ∈ B`.

Rewrite using `[map_add]`. Conclude with `B.add_mem ha hb`. Use the proof step `zero_mem' := by show φ 0 ∈ B; rw [map_zero]; exact B.zero_mem`. Use the proof step `algebraMap_mem' := fun r => by show φ (algebraMap ℂ κ r) ∈ B`. Establish `: φ (algebraMap ℂ κ r) = algebraMap κ' _ (algebraMap ℂ κ' r)` using `by show mk (algebraMap ℂ κ r ⊗ₜ 1) = mk (1 ⊗ₜ algebraMap ℂ κ' r)`.

Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Rewrite using `[this]`. Conclude with `B.algebraMap_mem _`. Use the proof step `inv_mem' := fun a ha => by show φ a⁻¹ ∈ B`. Distinguish the cases in `ha0 : a = 0`.

Rewrite using `[ha0, inv_zero, map_zero]`. Conclude with `B.zero_mem`. Establish `ha' : φ a ∈ B` using `ha`. Establish `hnil : IsNilpotent ((⟨φ a, ha'⟩ : B) - algebraMap κ' B (ρ a))`. Use `⟨M, Subtype.ext ?_⟩` and prove the remaining obligations.

Establish `h2` using `Ideal.pow_mem_pow (hφσ a) M`. Rewrite `h2` using `[hNM, Ideal.mem_bot]`. Simplify using `using h2`. Establish `hu : IsUnit (algebraMap κ' B (ρ a))` using `(isUnit_iff_ne_zero.2 ((map_ne_zero ρ).2 ha0)).map _`. Establish `hx : IsUnit (⟨φ a, ha'⟩ : B)`.

Use `hnil.isUnit_add_left_of_commute hu (Commute.all _ _)` as an intermediate fact. Simplify using `using this`. Take `⟨y, hy⟩` from `hx.exists_right_inv`. Establish `hy' : φ a * (y : (κ ⊗[ℂ] κ') ⧸ J ^ M) = 1` using `congrArg Subtype.val hy`. Establish `h2 : φ a⁻¹ * φ a = 1` using `by rw [← map_mul, inv_mul_cancel₀ ha0, map_one]`.

Establish `: φ a⁻¹ = y`. Combine the equalities or inequalities in the displayed calculation. Use `_ = y := by rw [← mul_assoc, h2, one_mul]`. Rewrite using `[this]`. Conclude with `y.2 }`.

Establish `hle : IntermediateField.adjoin ℂ (Set.range z) ≤ F`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hzB i`. Establish `eAlg : (algebraMap ℂ κ).toAlgebra = ‹Algebra ℂ κ›` using `Algebra.algebra_ext _ _ fun _ => rfl`.

Establish `hz' : IsTranscendenceBasis ℂ z`. Unfold `TrBasis at hz`. Rewrite `hz` using `[eAlg]`. Conclude with `hz`. Use `haveI := hz'.isAlgebraic_field`.

Use `letI : Algebra (IntermediateField.adjoin ℂ (Set.range z)) F := (IntermediateField.inclusion hle).toRingHom.toAlgebra`. Use `haveI : IsScalarTower (IntermediateField.adjoin ℂ (Set.range z)) F κ := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : Algebra.IsAlgebraic F κ := Algebra.IsAlgebraic.extendScalars (R := IntermediateField.adjoin ℂ (Set.range z)) (IntermediateField.inclusion_injective hle)`. Use `haveI : Algebra.IsSeparable F κ := Algebra.IsAlgebraic.isSeparable_of_perfectField`. Set `σ : κ →+* B.toSubring` to `((algebraMap κ' _).comp ρ.toRingHom).codRestrict B.toSubring (fun a => B.algebraMap_mem _)`.

Establish `key : ∀ a, φ a ∈ B` using `fun a => mem_of_formallyEtale φ B.toSubring (fun c : F => c.2) N hN σ (fun a => hφσ a) a`. Establish `hB : ∀ x, x ∈ B`. Introduce `x`. Take `⟨w, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Proceed by induction on `w using TensorProduct.induction_on with`.

Consider the case `zero => rw [map_zero]`. Conclude with `B.zero_mem`. Consider the case `tmul a b`. Establish `: Ideal.Quotient.mk (J ^ M) (a ⊗ₜ b) = φ a * algebraMap κ' _ b` using `by show mk _ = mk (a ⊗ₜ 1) * mk (1 ⊗ₜ b)`. Rewrite using `[← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.

Rewrite using `[this]`. Conclude with `B.mul_mem (key a) (B.algebraMap_mem b)`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `B.add_mem hx hy`. Establish `ht : ∀ i, t i ∈ N` using `fun i => hφσ (z i)`.

Set `f : Sym (Fin (k + 1)) (M - 1) → (κ ⊗[ℂ] κ') ⧸ J ^ M` to `fun s => ∏ i : Fin k, t i ^ ((s : Multiset (Fin (k + 1))).count i.castSucc)`. Establish `hmono : ∀ y ∈ Submonoid.closure (Set.range t), ∃ α : Fin k → ℕ, y = ∏ i, t i ^ α i`. Introduce `y hy`. Proceed by induction on `hy using Submonoid.closure_induction with`. Consider the case `mem y hy`.

Take `⟨i, rfl⟩` from `hy`. Conclude with `⟨Pi.single i 1, by simp [Pi.single_apply, pow_ite]⟩`. Consider the case `one => exact ⟨0, by simp⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨α, rfl⟩` from `hx`.

Take `⟨β, rfl⟩` from `hy`. Conclude with `⟨α + β, by simp [pow_add, Finset.prod_mul_distrib]⟩`. Establish `hspan : ∀ x, x ∈ Submodule.span κ' (Set.range f)`. Introduce `x`. Establish `hx : x ∈ Subalgebra.toSubmodule B` using `hB x`.

Rewrite `hx` using `[Algebra.adjoin_eq_span]`. Use `Submodule.span_le.2 ?_ hx` and prove the remaining obligations. Introduce `y hy`. Take `⟨α, rfl⟩` from `hmono y hy`. Distinguish the cases in `hα : ∑ i, α i < M`.

Set `g : Fin (k + 1) → ℕ` to `Fin.snoc α (M - 1 - ∑ i, α i)`. Set `m : Multiset (Fin (k + 1))` to `Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm g)`. Establish `hcard : Multiset.card m = M - 1`. Simplify using `only [m, Finsupp.card_toMultiset]`. Rewrite using `[Finsupp.sum_fintype _ _ (fun _ => rfl)]`.

Express the relevant statement in the definitionally equal form `∑ j, g j = M - 1`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [g, Fin.snoc_castSucc, Fin.snoc_last]`. Use linear arithmetic over natural numbers and integers. Use `Submodule.subset_span ⟨⟨m, hcard⟩, ?_⟩` and prove the remaining obligations.

Simplify using `only [f]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[m, g, Finsupp.count_toMultiset]`. Establish `h1 : ∏ i, t i ^ α i ∈ ∏ i : Fin k, N ^ α i` using `Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (ht i) _`. Rewrite `h1` using `[Finset.prod_pow_eq_pow_sum]`.

Establish `h2` using `Ideal.pow_le_pow_right (not_lt.1 hα) h1`. Rewrite `h2` using `[hNM, Ideal.mem_bot]`. Rewrite using `[h2]`. Conclude with `Submodule.zero_mem _`. Establish `htop : Submodule.span κ' (Set.range f) = ⊤` using `eq_top_iff.2 fun x _ => hspan x`.

Use `⟨?_, ⟨htop ▸ Submodule.fg_span (Set.finite_range f)⟩⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Sym.card_sym_eq_choose, Fintype.card_fin]`. Establish `e : k + 1 + (M - 1) - 1 = M + k - 1` using `by omega`. Rewrite using `[e]`.

Conclude with `Nat.choose_symm_of_eq_add (by omega)`.
-/
theorem jets_finrank_le : ∀ {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ'] (k M : ℕ) (ρ : κ →ₐ[ℂ] κ'),
  (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  letI : Algebra κ' (κ ⊗[ℂ] κ') := Algebra.TensorProduct.rightAlgebra;
  Module.finrank κ' ((κ ⊗[ℂ] κ') ⧸ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M) ≤
    (M + k - 1).choose k ∧
  Module.Finite κ' ((κ ⊗[ℂ] κ') ⧸ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M) := by
  intro κ κ' _ _ _ _ k M ρ hz0
  letI : Algebra κ' (κ ⊗[ℂ] κ') := Algebra.TensorProduct.rightAlgebra
  obtain ⟨z, hz⟩ := hz0
  set J := RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ')) with hJ
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · haveI : Subsingleton ((κ ⊗[ℂ] κ') ⧸ J ^ 0) :=
      Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top])
    exact ⟨by rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _, inferInstance⟩
  let mk : κ ⊗[ℂ] κ' →+* (κ ⊗[ℂ] κ') ⧸ J ^ M := Ideal.Quotient.mk (J ^ M)
  let φ : κ →+* (κ ⊗[ℂ] κ') ⧸ J ^ M := mk.comp Algebra.TensorProduct.includeLeftRingHom
  let N : Ideal ((κ ⊗[ℂ] κ') ⧸ J ^ M) := J.map mk
  have hNM : N ^ M = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]
  have hN : IsNilpotent N := ⟨M, by rw [Ideal.zero_eq_bot]; exact hNM⟩
  have hφσ : ∀ a, φ a - algebraMap κ' _ (ρ a) ∈ N := by
    intro a
    have e : φ a - algebraMap κ' _ (ρ a) = mk (a ⊗ₜ 1 - 1 ⊗ₜ ρ a) := by rw [map_sub]; rfl
    rw [e]
    refine Ideal.mem_map_of_mem _ ?_
    simp [hJ, RingHom.mem_ker, Algebra.TensorProduct.productMap_apply_tmul]
  let t : Fin k → (κ ⊗[ℂ] κ') ⧸ J ^ M := fun i => φ (z i) - algebraMap κ' _ (ρ (z i))
  let B : Subalgebra κ' ((κ ⊗[ℂ] κ') ⧸ J ^ M) := Algebra.adjoin κ' (Set.range t)
  have hzB : ∀ i, φ (z i) ∈ B := by
    intro i
    have : φ (z i) = t i + algebraMap κ' _ (ρ (z i)) := by simp [t]
    rw [this]
    exact B.add_mem (Algebra.subset_adjoin ⟨i, rfl⟩) (B.algebraMap_mem _)

  let F : IntermediateField ℂ κ :=
    { carrier := {a | φ a ∈ B}
      mul_mem' := fun {a b} ha hb => by
        show φ (a * b) ∈ B
        rw [map_mul]; exact B.mul_mem ha hb
      one_mem' := by show φ 1 ∈ B; rw [map_one]; exact B.one_mem
      add_mem' := fun {a b} ha hb => by
        show φ (a + b) ∈ B
        rw [map_add]; exact B.add_mem ha hb
      zero_mem' := by show φ 0 ∈ B; rw [map_zero]; exact B.zero_mem
      algebraMap_mem' := fun r => by
        show φ (algebraMap ℂ κ r) ∈ B
        have : φ (algebraMap ℂ κ r) = algebraMap κ' _ (algebraMap ℂ κ' r) := by
          show mk (algebraMap ℂ κ r ⊗ₜ 1) = mk (1 ⊗ₜ algebraMap ℂ κ' r)
          rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
        rw [this]; exact B.algebraMap_mem _
      inv_mem' := fun a ha => by
        show φ a⁻¹ ∈ B
        by_cases ha0 : a = 0
        · rw [ha0, inv_zero, map_zero]; exact B.zero_mem
        have ha' : φ a ∈ B := ha
        have hnil : IsNilpotent ((⟨φ a, ha'⟩ : B) - algebraMap κ' B (ρ a)) := by
          refine ⟨M, Subtype.ext ?_⟩
          have h2 := Ideal.pow_mem_pow (hφσ a) M
          rw [hNM, Ideal.mem_bot] at h2
          simpa using h2
        have hu : IsUnit (algebraMap κ' B (ρ a)) :=
          (isUnit_iff_ne_zero.2 ((map_ne_zero ρ).2 ha0)).map _
        have hx : IsUnit (⟨φ a, ha'⟩ : B) := by
          have := hnil.isUnit_add_left_of_commute hu (Commute.all _ _)
          simpa using this
        obtain ⟨y, hy⟩ := hx.exists_right_inv
        have hy' : φ a * (y : (κ ⊗[ℂ] κ') ⧸ J ^ M) = 1 := congrArg Subtype.val hy
        have h2 : φ a⁻¹ * φ a = 1 := by rw [← map_mul, inv_mul_cancel₀ ha0, map_one]
        have : φ a⁻¹ = y := by
          calc φ a⁻¹ = φ a⁻¹ * (φ a * y) := by rw [hy', mul_one]
          _ = y := by rw [← mul_assoc, h2, one_mul]
        rw [this]; exact y.2 }
  have hle : IntermediateField.adjoin ℂ (Set.range z) ≤ F := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact hzB i
  have eAlg : (algebraMap ℂ κ).toAlgebra = ‹Algebra ℂ κ› := Algebra.algebra_ext _ _ fun _ => rfl
  have hz' : IsTranscendenceBasis ℂ z := by
    unfold TrBasis at hz
    rw [eAlg] at hz
    exact hz
  haveI := hz'.isAlgebraic_field
  letI : Algebra (IntermediateField.adjoin ℂ (Set.range z)) F :=
    (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower (IntermediateField.adjoin ℂ (Set.range z)) F κ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic F κ :=
    Algebra.IsAlgebraic.extendScalars (R := IntermediateField.adjoin ℂ (Set.range z))
      (IntermediateField.inclusion_injective hle)
  haveI : Algebra.IsSeparable F κ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let σ : κ →+* B.toSubring :=
    ((algebraMap κ' _).comp ρ.toRingHom).codRestrict B.toSubring (fun a => B.algebraMap_mem _)
  have key : ∀ a, φ a ∈ B := fun a =>
    mem_of_formallyEtale φ B.toSubring (fun c : F => c.2) N hN σ (fun a => hφσ a) a
  have hB : ∀ x, x ∈ B := by
    intro x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact B.zero_mem
    | tmul a b =>
      have : Ideal.Quotient.mk (J ^ M) (a ⊗ₜ b) = φ a * algebraMap κ' _ b := by
        show mk _ = mk (a ⊗ₜ 1) * mk (1 ⊗ₜ b)
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]; exact B.mul_mem (key a) (B.algebraMap_mem b)
    | add x y hx hy => rw [map_add]; exact B.add_mem hx hy

  have ht : ∀ i, t i ∈ N := fun i => hφσ (z i)
  let f : Sym (Fin (k + 1)) (M - 1) → (κ ⊗[ℂ] κ') ⧸ J ^ M :=
    fun s => ∏ i : Fin k, t i ^ ((s : Multiset (Fin (k + 1))).count i.castSucc)
  have hmono : ∀ y ∈ Submonoid.closure (Set.range t), ∃ α : Fin k → ℕ, y = ∏ i, t i ^ α i := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨Pi.single i 1, by simp [Pi.single_apply, pow_ite]⟩
    | one => exact ⟨0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨α, rfl⟩ := hx
      obtain ⟨β, rfl⟩ := hy
      exact ⟨α + β, by simp [pow_add, Finset.prod_mul_distrib]⟩
  have hspan : ∀ x, x ∈ Submodule.span κ' (Set.range f) := by
    intro x
    have hx : x ∈ Subalgebra.toSubmodule B := hB x
    rw [Algebra.adjoin_eq_span] at hx
    refine Submodule.span_le.2 ?_ hx
    intro y hy
    obtain ⟨α, rfl⟩ := hmono y hy
    by_cases hα : ∑ i, α i < M
    · let g : Fin (k + 1) → ℕ := Fin.snoc α (M - 1 - ∑ i, α i)
      let m : Multiset (Fin (k + 1)) := Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm g)
      have hcard : Multiset.card m = M - 1 := by
        simp only [m, Finsupp.card_toMultiset]
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        change ∑ j, g j = M - 1
        rw [Fin.sum_univ_castSucc]
        simp only [g, Fin.snoc_castSucc, Fin.snoc_last]
        omega
      refine Submodule.subset_span ⟨⟨m, hcard⟩, ?_⟩
      simp only [f]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [m, g, Finsupp.count_toMultiset]
    · have h1 : ∏ i, t i ^ α i ∈ ∏ i : Fin k, N ^ α i :=
        Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (ht i) _
      rw [Finset.prod_pow_eq_pow_sum] at h1
      have h2 := Ideal.pow_le_pow_right (not_lt.1 hα) h1
      rw [hNM, Ideal.mem_bot] at h2
      rw [h2]
      exact Submodule.zero_mem _
  have htop : Submodule.span κ' (Set.range f) = ⊤ := eq_top_iff.2 fun x _ => hspan x
  refine ⟨?_, ⟨htop ▸ Submodule.fg_span (Set.finite_range f)⟩⟩
  calc Module.finrank κ' ((κ ⊗[ℂ] κ') ⧸ J ^ M)
      = Module.finrank κ' (⊤ : Submodule κ' ((κ ⊗[ℂ] κ') ⧸ J ^ M)) := (finrank_top _ _).symm
    _ = Module.finrank κ' (Submodule.span κ' (Set.range f)) := by rw [htop]
    _ ≤ Fintype.card (Sym (Fin (k + 1)) (M - 1)) := finrank_range_le_card f
    _ = (M + k - 1).choose k := by
      rw [Sym.card_sym_eq_choose, Fintype.card_fin]
      have e : k + 1 + (M - 1) - 1 = M + k - 1 := by omega
      rw [e]
      exact Nat.choose_symm_of_eq_add (by omega)

end GlobalTheory.JetDim
