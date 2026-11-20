import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LenCob
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MatKOSmulOne

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.Cob

/- English proof (translation)
Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Establish `: Subsingleton (KOG O 0)` using `(Submodule.Quotient.mk_surjective _).subsingleton`. Rewrite using `[Module.length_eq_zero]`. Conclude with `zero_le`. Break down `eq_or_ne a 0 with rfl | ha` into its components or cases.

Establish `e : (O ⧸ Ideal.span {(0 : O)}) ≃ₗ[O] O` using `Submodule.quotEquivOfEqBot _ (by simp)`. Rewrite using `[e.length_eq]`. Establish `: Module.length O O = ⊤`. Assume the negation of the conclusion as `h`. Establish `h2` using `(isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h)).2`.

Establish `: IsArtinianRing O` using `h2`. Conclude with `IsDiscreteValuationRing.not_isField O (IsArtinianRing.isField_of_isDomain O)`. Rewrite using `[this, ENat.mul_top (by exact_mod_cast hk.ne')]; exact le_top`. Establish `ha' : algebraMap O (FractionRing O) a ≠ 0`. Simplify using `using ha`.

Set `x : Fin k → KOG O k` to `fun j => Submodule.Quotient.mk (Pi.single j (algebraMap O (FractionRing O) a)⁻¹)`. Establish `hx : ∀ j, a • x j = 0`. Introduce `j`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Use `⟨Pi.single j 1, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `j'`. Distinguish the cases in `h : j' = j`. Substitute `h` using the available equality. Simplify using `[Algebra.smul_def, mul_inv_cancel₀ ha']`. Simplify using `[h]`.

Set `f : Fin k → O →ₗ[O] Submodule.torsionBy O (KOG O k) a` to `fun j => LinearMap.toSpanSingleton O _ ⟨x j, hx j⟩`. Establish `hf : ∀ j, Ideal.span {a} ≤ LinearMap.ker (f j)`. Introduce `j`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Subtype.ext (hx j)`.

Set `F : (Fin k → O ⧸ Ideal.span {a}) →ₗ[O] Submodule.torsionBy O (KOG O k) a` to `∑ j, (Submodule.liftQ _ (f j) (hf j)).comp (LinearMap.proj j)`. Establish `hl : Module.length O (Fin k → O ⧸ Ideal.span {a}) = (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {a})`. Rewrite using `[Module.length_pi_of_fintype]`. Simplify using the standard rewrite rules. Rewrite using `[← hl]`.

Use `Module.length_le_of_surjective F ?_` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Proceed by induction on `y using Submodule.Quotient.induction_on with`. Consider the case `H y`. Establish `hy'` using `hy`.

Rewrite `hy'` using `[Submodule.mem_torsionBy_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Take `⟨b, hb⟩` from `hy'`. Use `⟨fun j => Submodule.Quotient.mk (b j), Subtype.ext ?_⟩` and prove the remaining obligations. Establish `e : ((F fun j => Submodule.Quotient.mk (b j) : Submodule.torsionBy O (KOG O k) a) : KOG O k) = ∑ j, b j • x j`. Simplify using `only [F, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Express the relevant statement in the definitionally equal form `∑ j, b j • (stdG O (FractionRing O) k).mkQ _ = (stdG O (FractionRing O) k).mkQ y`. Simplify using `only [← map_smul, ← map_sum]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Establish `h0 : algebraMap O (FractionRing O) (b j) = algebraMap O (FractionRing O) a * y j`. Simplify `congrFun hb j` using `[Algebra.smul_def]`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single j (fun j' _ h => by simp [Ne.symm h]) (by simp)]`. Simplify using `only [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, h0]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem length_torsionBy_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (k : ℕ) (a : O) :
    Module.length O (Submodule.torsionBy O (KOG O k) a) ≤ (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : Subsingleton (KOG O 0) := (Submodule.Quotient.mk_surjective _).subsingleton
    rw [Module.length_eq_zero]
    exact zero_le
  rcases eq_or_ne a 0 with rfl | ha
  · have e : (O ⧸ Ideal.span {(0 : O)}) ≃ₗ[O] O := Submodule.quotEquivOfEqBot _ (by simp)
    rw [e.length_eq]
    have : Module.length O O = ⊤ := by
      by_contra h
      have h2 := (isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h)).2
      have : IsArtinianRing O := h2
      exact IsDiscreteValuationRing.not_isField O (IsArtinianRing.isField_of_isDomain O)
    rw [this, ENat.mul_top (by exact_mod_cast hk.ne')]; exact le_top
  · have ha' : algebraMap O (FractionRing O) a ≠ 0 := by
      simpa using ha
    let x : Fin k → KOG O k := fun j => Submodule.Quotient.mk (Pi.single j (algebraMap O (FractionRing O) a)⁻¹)
    have hx : ∀ j, a • x j = 0 := by
      intro j
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      refine ⟨Pi.single j 1, ?_⟩
      funext j'
      by_cases h : j' = j
      · subst h
        simp [Algebra.smul_def, mul_inv_cancel₀ ha']
      · simp [h]
    let f : Fin k → O →ₗ[O] Submodule.torsionBy O (KOG O k) a := fun j =>
      LinearMap.toSpanSingleton O _ ⟨x j, hx j⟩
    have hf : ∀ j, Ideal.span {a} ≤ LinearMap.ker (f j) := by
      intro j
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Subtype.ext (hx j)
    let F : (Fin k → O ⧸ Ideal.span {a}) →ₗ[O] Submodule.torsionBy O (KOG O k) a :=
      ∑ j, (Submodule.liftQ _ (f j) (hf j)).comp (LinearMap.proj j)
    have hl : Module.length O (Fin k → O ⧸ Ideal.span {a}) = (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
      rw [Module.length_pi_of_fintype]
      simp
    rw [← hl]
    refine Module.length_le_of_surjective F ?_
    rintro ⟨y, hy⟩
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      have hy' := hy
      rw [Submodule.mem_torsionBy_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hy'
      obtain ⟨b, hb⟩ := hy'
      refine ⟨fun j => Submodule.Quotient.mk (b j), Subtype.ext ?_⟩
      have e : ((F fun j => Submodule.Quotient.mk (b j) : Submodule.torsionBy O (KOG O k) a) : KOG O k) =
          ∑ j, b j • x j := by
        simp only [F, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum]
        rfl
      rw [e]
      change ∑ j, b j • (stdG O (FractionRing O) k).mkQ _ = (stdG O (FractionRing O) k).mkQ y
      simp only [← map_smul, ← map_sum]
      congr 1
      funext j
      have h0 : algebraMap O (FractionRing O) (b j) = algebraMap O (FractionRing O) a * y j := by
        simpa [Algebra.smul_def] using congrFun hb j
      rw [Finset.sum_apply, Finset.sum_eq_single j (fun j' _ h => by simp [Ne.symm h]) (by simp)]
      simp only [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, h0]
      field_simp

/- English proof (translation)
Break down `eq_or_ne a 0 with rfl | ha` into its components or cases. Rewrite using `[mul_zero, two_mul]`. Conclude with `le_self_add`. Rewrite using `[two_mul]`. Conclude with `(Ring.ord_mul O (mem_nonZeroDivisors_of_ne_zero ha)).le`.
-/
theorem length_sq_le {O : Type} [CommRing O] [IsDomain O] (a : O) :
    Module.length O (O ⧸ Ideal.span {a * a}) ≤ 2 * Module.length O (O ⧸ Ideal.span {a}) := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [mul_zero, two_mul]
    exact le_self_add
  · rw [two_mul]
    exact (Ring.ord_mul O (mem_nonZeroDivisors_of_ne_zero ha)).le

/- English proof (translation)
Establish `h1 : C ⊓ (ReciprocityTheory.Gal.B1 σ : Submodule O (Γ → KOG O k)) ≤ (Submodule.torsionBy O (KOG O k) (a * a)).map (d0 σ)`. Introduce and unpack `_ ⟨hc, w, rfl⟩`. Conclude with `⟨w, h w hc, rfl⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem length_inf_coboundaries_le_two_mul_rank {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] {k : ℕ} (σ : Representation O Γ (KOG O k)) (C : Submodule O (Γ → KOG O k)) (a : O)
    (h : ∀ w, d0 σ w ∈ C → (a * a) • w = 0) :
    Module.length O ↥(C ⊓ (ReciprocityTheory.Gal.B1 σ : Submodule O (Γ → KOG O k))) ≤
      ((2 * k : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  have h1 : C ⊓ (ReciprocityTheory.Gal.B1 σ : Submodule O (Γ → KOG O k)) ≤
      (Submodule.torsionBy O (KOG O k) (a * a)).map (d0 σ) := by
    rintro _ ⟨hc, w, rfl⟩
    exact ⟨w, h w hc, rfl⟩
  calc _ ≤ Module.length O ↥((Submodule.torsionBy O (KOG O k) (a * a)).map (d0 σ)) :=
        Module.length_le_of_injective (Submodule.inclusion h1) (Submodule.inclusion_injective h1)
    _ ≤ Module.length O ↥(Submodule.torsionBy O (KOG O k) (a * a)) :=
        Module.length_le_of_surjective ((d0 σ).submoduleMap _) (LinearMap.submoduleMap_surjective _ _)
    _ ≤ (k : ℕ∞) * (2 * Module.length O (O ⧸ Ideal.span {a})) :=
        (length_torsionBy_le k _).trans (mul_le_mul_right (length_sq_le a) _)
    _ = _ := by push_cast; ring

section Span

variable {D : D7} {i : D.nd.Loc} {X' : Type} {T' : Subalgebra (D.nd.O i) (X' → D.nd.O i)}
  {rep : X' → (GE D.nd →* MatN D.nd i)}

/- English proof (translation)
Assemble the required witnesses or components as `⟨Fintype.card ι, fun k => f ((Fintype.equivFin ι).symm k), fun k => g ((Fintype.equivFin ι).symm k), fun _ => hf _, (Equiv.sum_comp (Fintype.equivFin ι).symm fun k => fun x' => f k x' • rep x' (g k)).symm⟩`.
-/
theorem inSpan_of_fintype {ι : Type} [Fintype ι] (f : ι → X' → D.nd.O i) (g : ι → GE D.nd) (hf : ∀ k, f k ∈ T') :
    InSpan D.nd i T' rep (∑ k, fun x' => f k x' • rep x' (g k)) :=
  ⟨Fintype.card ι, fun k => f ((Fintype.equivFin ι).symm k), fun k => g ((Fintype.equivFin ι).symm k),
    fun _ => hf _, (Equiv.sum_comp (Fintype.equivFin ι).symm fun k => fun x' => f k x' • rep x' (g k)).symm⟩

/- English proof (translation)
Take `⟨m, f, g, hf, rfl⟩` from `ha`. Take `⟨m', f', g', hf', rfl⟩` from `hb`. Use `inSpan_of_fintype (T' := T') (rep := rep) (Sum.elim f f') (Sum.elim g g') (by rintro (k | k); exacts [hf k, hf' k])` as an intermediate fact. Rewrite `this` using `[Fintype.sum_sum_type]`. Conclude with `this`.
-/
theorem inSpan_add {a b : X' → MatN D.nd i} (ha : InSpan D.nd i T' rep a) (hb : InSpan D.nd i T' rep b) :
    InSpan D.nd i T' rep (a + b) := by
  obtain ⟨m, f, g, hf, rfl⟩ := ha
  obtain ⟨m', f', g', hf', rfl⟩ := hb
  have := inSpan_of_fintype (T' := T') (rep := rep) (Sum.elim f f') (Sum.elim g g') (by rintro (k | k); exacts [hf k, hf' k])
  rw [Fintype.sum_sum_type] at this
  exact this

/- English proof (translation)
Take `⟨m, f, g, hf, rfl⟩` from `ha`. Take `⟨m', f', g', hf', rfl⟩` from `hb`. Use `inSpan_of_fintype (T' := T') (rep := rep) (fun p : Fin m × Fin m' => f p.1 * f' p.2) (fun p => g p.1 * g' p.2) (fun p => mul_mem (hf _) (hf' _))` as an intermediate fact. Rewrite `this` using `[Fintype.sum_prod_type]`. Rewrite using `[Finset.sum_mul_sum]`.

Use `this using 3 with k _ k' _` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x'`. Simplify using `only [Pi.mul_apply, map_mul, smul_mul_smul_comm]`.
-/
theorem inSpan_mul {a b : X' → MatN D.nd i} (ha : InSpan D.nd i T' rep a) (hb : InSpan D.nd i T' rep b) :
    InSpan D.nd i T' rep (a * b) := by
  obtain ⟨m, f, g, hf, rfl⟩ := ha
  obtain ⟨m', f', g', hf', rfl⟩ := hb
  have := inSpan_of_fintype (T' := T') (rep := rep) (fun p : Fin m × Fin m' => f p.1 * f' p.2)
    (fun p => g p.1 * g' p.2) (fun p => mul_mem (hf _) (hf' _))
  rw [Fintype.sum_prod_type] at this
  rw [Finset.sum_mul_sum]
  convert this using 3 with k _ k' _
  funext x'
  simp only [Pi.mul_apply, map_mul, smul_mul_smul_comm]

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, fun _ => f, fun _ => 1, fun _ => hf, by funext x; simp⟩`.
-/
theorem inSpan_scalar {f : X' → D.nd.O i} (hf : f ∈ T') :
    InSpan D.nd i T' rep fun x' => f x' • (1 : MatN D.nd i) :=
  ⟨1, fun _ => f, fun _ => 1, fun _ => hf, by funext x; simp⟩

end Span

variable {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
  {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i} {S : IdempotentChoiceData D.nd i}

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, ⟨hT, -⟩, -⟩` from `hS`. Take `⟨m, f, g, hf, rfl⟩` from `ha`. Conclude with `⟨m, fun k x' => f k (S.p x'), g, fun k => hT _ (hf k), by funext x'; simp only [Finset.sum_apply]⟩`.
-/
theorem inR'_comp (hS : GoodCongruenceObjects D.nd r ρ π S) {a : D.nd.X i → MatN D.nd i} (ha : InR D.nd i r a) :
    InR' D.nd r S fun x' => a (S.p x') := by
  obtain ⟨-, -, -, -, -, -, -, ⟨hT, -⟩, -⟩ := hS
  obtain ⟨m, f, g, hf, rfl⟩ := ha
  exact ⟨m, fun k x' => f k (S.p x'), g, fun k => hT _ (hf k), by funext x'; simp only [Finset.sum_apply]⟩

/- English proof (translation)
Establish `hB` using `inR'_comp hS hS.1.1`. Establish `hX` using `inR'_comp hS hS.2.2.2.2.2.2.1.1`. Establish `hr` using `hS.2.2.2.2.2.2.2.1.2.1`. Establish `key : ∀ L : List ℕ, (∀ c ∈ L, c ∈ Finset.Icc 1 D.R.t) → InR' D.nd r S fun x' => (L.map fun c => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')).prod`. Introduce `L`.

Proceed by induction on `L with`. Consider the case `nil => exact fun _ => Check.inR'_one i r S`. Consider the case `cons c L ih`. Introduce `h`. Establish `h1` using `inSpan_mul (inSpan_add hX (inSpan_mul (inSpan_scalar (neg_mem (hr c (h c (by simp))))) hB)) (ih fun c hc => h c (by simp [hc]))`.

Use `Eq.mp (congrArg (InR' D.nd r S) ?_) h1` and prove the remaining obligations. Use function extensionality and compare the values at `x'`. Simplify using `[sub_eq_add_neg]`. Use `key _ fun c hc => ?_` and prove the remaining obligations. Rewrite `hc` using `[List.mem_range'_1]`.

Rewrite using `[Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers.
-/
theorem inR'_Eel (hS : GoodCongruenceObjects D.nd r ρ π S) : InR' D.nd r S (Eel D.nd S) := by
  have hB := inR'_comp hS hS.1.1
  have hX := inR'_comp hS hS.2.2.2.2.2.2.1.1
  have hr := hS.2.2.2.2.2.2.2.1.2.1
  have key : ∀ L : List ℕ, (∀ c ∈ L, c ∈ Finset.Icc 1 D.R.t) → InR' D.nd r S fun x' =>
      (L.map fun c => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')).prod := by
    intro L
    induction L with
    | nil => exact fun _ => Check.inR'_one i r S
    | cons c L ih =>
      intro h
      have h1 := inSpan_mul (inSpan_add hX (inSpan_mul (inSpan_scalar (neg_mem (hr c (h c (by simp))))) hB))
        (ih fun c hc => h c (by simp [hc]))
      refine Eq.mp (congrArg (InR' D.nd r S) ?_) h1
      funext x'
      simp [sub_eq_add_neg]
  refine key _ fun c hc => ?_
  rw [List.mem_range'_1] at hc
  rw [Finset.mem_Icc]
  omega

/- English proof (translation)
Establish `hr` using `hS.2.2.2.2.2.2.2.1.2.1`. Establish `: del51 D.nd S = ∏ c ∈ Finset.Ioc 1 D.R.t, (S.rr 1 - S.rr c)`. Use function extensionality and compare the values at `x'`. Simplify using `[del51, Finset.prod_apply]`. Rewrite using `[this]`.

Apply the tactic sequence `refine prod_mem fun c hc => sub_mem (hr 1 ?_) (hr c ?_) <;>`. Rewrite `hc` using `[Finset.mem_Ioc]`. Rewrite using `[Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers.
-/
theorem del_mem (hS : GoodCongruenceObjects D.nd r ρ π S) : del51 D.nd S ∈ S.T' := by
  have hr := hS.2.2.2.2.2.2.2.1.2.1
  have : del51 D.nd S = ∏ c ∈ Finset.Ioc 1 D.R.t, (S.rr 1 - S.rr c) := by
    funext x'
    simp [del51, Finset.prod_apply]
  rw [this]
  refine prod_mem fun c hc => sub_mem (hr 1 ?_) (hr c ?_) <;>
  · rw [Finset.mem_Ioc] at hc
    rw [Finset.mem_Icc]
    omega

/- English proof (translation)
Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem c hc`. Take `⟨φ, h1, -, rfl⟩` from `hc`. Establish `hE2` using `hS.2.2.2.2.2.2.2.2.2.2.1.2.1`. Set `s : Fin m → S.X' → D.nd.O i` to `fun j => ((chiU D.nd i 1 (g j) : (D.nd.O i)ˣ) : D.nd.O i) • f j`.

Establish `hs : ∀ j, s j ∈ S.T'` using `fun j => S.T'.smul_mem (hf j) _`. Set `z : S.X' → MatN D.nd i` to `∑ j, (fun x' => s j x' • (1 : MatN D.nd i)) * yg D.nd r S (g j)`. Establish `hz : InY D.nd r S z` using `⟨m, _, g, fun j => inSpan_scalar (hs j), rfl⟩`. Establish `hz1 : ∀ x', z x' = (del51 D.nd S x' - ∑ j, s j x') • Eel D.nd S x'`. Introduce `x'`.

Rewrite using `[sub_smul, ← hE2, Finset.sum_smul]`. Use `nth_rewrite 1 [congrFun e x']`. Simplify using `only [z, Finset.sum_apply]`. Rewrite using `[Finset.sum_mul, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.mul_apply, yg, s, Pi.smul_apply, smul_eq_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul]`. Rewrite using `[mul_right_comm, Units.mul_inv, one_mul]`. Establish `hz2 : Eel D.nd S * z = (fun x' => del51 D.nd S x' • (1 : MatN D.nd i)) * z`. Use function extensionality and compare the values at `x'`. Simplify using `only [Pi.mul_apply, hz1, mul_smul_comm, hE2, smul_mul_assoc, one_mul]`.

Establish `h2` using `congrArg φ hz2`. Rewrite `h2` using `[h1 _ (inR'_Eel hS) _ hz, h1 _ (inSpan_scalar (del_mem hS)) _ hz, hE, hψ _ (del_mem hS), Check.matKO_smul_one, ← zero_smul (D.nd.O i) (1 : Matrix (Fin k) (Fin k) (D.nd.O i)), Check.matKO_smul_one, zero_smul]`. Rewrite using `[h2]`. Use `congr 1`. Simplify using `only [z, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[h1 _ (inSpan_scalar (hs j)) _ (Check.inY_yg i r S _), hψ _ (hs j), Check.matKO_smul_one]`. Both sides reduce to the same expression. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib, ha, hb, add_zero]`.

Consider the case `smul a b _ hb`. Simplify using `only [Pi.smul_apply, smul_comm _ a, ← Finset.smul_sum]`. Rewrite using `[hb, smul_zero]`.
-/
theorem del_smul_sum (hS : GoodCongruenceObjects D.nd r ρ π S) (Xs : Set (D.nd.X i)) {k : ℕ}
    (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) (hE : ψ (Eel D.nd S) = 0)
    (hψ : ∀ f ∈ S.T', ψ (fun x' => f x' • (1 : MatN D.nd i)) = f S.π' • 1)
    {m : ℕ} {f : Fin m → S.X' → D.nd.O i} {g : Fin m → GE D.nd} (hf : ∀ j, f j ∈ S.T')
    (e : Eel D.nd S = ∑ j, fun x' => f j x' • rO D.nd i r (S.p x') (g j))
    {c : GE D.nd → KOG (D.nd.O i) k} (hc : c ∈ cocW i r S Xs ψ) :
    del51 D.nd S S.π' • ∑ j, (((chiU D.nd i 1 (g j) : (D.nd.O i)ˣ) : D.nd.O i) * f j S.π') • c (g j) = 0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨φ, h1, -, rfl⟩ := hc
    have hE2 := hS.2.2.2.2.2.2.2.2.2.2.1.2.1
    let s : Fin m → S.X' → D.nd.O i := fun j => ((chiU D.nd i 1 (g j) : (D.nd.O i)ˣ) : D.nd.O i) • f j
    have hs : ∀ j, s j ∈ S.T' := fun j => S.T'.smul_mem (hf j) _
    let z : S.X' → MatN D.nd i := ∑ j, (fun x' => s j x' • (1 : MatN D.nd i)) * yg D.nd r S (g j)
    have hz : InY D.nd r S z := ⟨m, _, g, fun j => inSpan_scalar (hs j), rfl⟩
    have hz1 : ∀ x', z x' = (del51 D.nd S x' - ∑ j, s j x') • Eel D.nd S x' := by
      intro x'
      rw [sub_smul, ← hE2, Finset.sum_smul]
      nth_rewrite 1 [congrFun e x']
      simp only [z, Finset.sum_apply]
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.mul_apply, yg, s, Pi.smul_apply, smul_eq_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul]
      rw [mul_right_comm, Units.mul_inv, one_mul]
    have hz2 : Eel D.nd S * z = (fun x' => del51 D.nd S x' • (1 : MatN D.nd i)) * z := by
      funext x'
      simp only [Pi.mul_apply, hz1, mul_smul_comm, hE2, smul_mul_assoc, one_mul]
    have h2 := congrArg φ hz2
    rw [h1 _ (inR'_Eel hS) _ hz, h1 _ (inSpan_scalar (del_mem hS)) _ hz, hE, hψ _ (del_mem hS),
      Check.matKO_smul_one, ← zero_smul (D.nd.O i) (1 : Matrix (Fin k) (Fin k) (D.nd.O i)),
      Check.matKO_smul_one, zero_smul] at h2
    rw [h2]
    congr 1
    simp only [z, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1 _ (inSpan_scalar (hs j)) _ (Check.inY_yg i r S _), hψ _ (hs j), Check.matKO_smul_one]
    rfl
  | zero => simp
  | add a b _ _ ha hb => simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib, ha, hb, add_zero]
  | smul a b _ hb =>
    simp only [Pi.smul_apply, smul_comm _ a, ← Finset.smul_sum]
    rw [hb, smul_zero]

/- English proof (translation)
Apply `Matrix.map_injective (IsFractionRing.injective (D.nd.O i) (KK D.nd i))` to reduce the goal to its premises. Conclude with `Matrix.mulVec_injective (funext h)`.
-/
theorem mat_ext {k : ℕ} {A B : Matrix (Fin k) (Fin k) (D.nd.O i)}
    (h : ∀ v, (A.map (toK D.nd i)).mulVec v = (B.map (toK D.nd i)).mulVec v) : A = B := by
  apply Matrix.map_injective (IsFractionRing.injective (D.nd.O i) (KK D.nd i))
  exact Matrix.mulVec_injective (funext h)

/- English proof (translation)
Rewrite using `[← Matrix.smul_mulVec]`. Use `congr 1`. Use extensionality with `p q`. Simplify using the standard rewrite rules.
-/
theorem map_smul_mulVec {k : ℕ} (a : D.nd.O i) (A : Matrix (Fin k) (Fin k) (D.nd.O i)) (v : Fin k → KK D.nd i) :
    ((a • A).map (toK D.nd i)).mulVec v = toK D.nd i a • (A.map (toK D.nd i)).mulVec v := by
  rw [← Matrix.smul_mulVec]
  congr 1
  ext p q
  simp

/- English proof (translation)
Establish `h` using `fun u => hS.2.2.1 _ (inSpan_scalar hf) (S.e.symm u)`. Simplify using `only [map_smul_mulVec, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec, map_smul, LinearEquiv.apply_symm_apply] at h`. Use `⟨mat_ext fun v => ?_, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul_mulVec, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]`. Conclude with `(congrArg Prod.fst (h (v, 0))).symm`.

Use `congrFun (congrArg Prod.snd (h (0, fun _ => 1))) c` as an intermediate fact. Simplify using `only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_one] at this`. Conclude with `(IsFractionRing.injective _ _ this).symm`.
-/
theorem psi_scalar (hS : GoodCongruenceObjects D.nd r ρ π S) {f : S.X' → D.nd.O i} (hf : f ∈ S.T') :
    S.ψρ (fun x' => f x' • (1 : MatN D.nd i)) = f S.π' • 1 ∧
      ∀ c, S.ψχ c (fun x' => f x' • (1 : MatN D.nd i)) = f S.π' := by
  have h := fun u => hS.2.2.1 _ (inSpan_scalar hf) (S.e.symm u)
  simp only [map_smul_mulVec, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec, map_smul,
    LinearEquiv.apply_symm_apply] at h
  refine ⟨mat_ext fun v => ?_, fun c => ?_⟩
  · rw [map_smul_mulVec, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact (congrArg Prod.fst (h (v, 0))).symm
  · have := congrFun (congrArg Prod.snd (h (0, fun _ => 1))) c
    simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_one] at this
    exact (IsFractionRing.injective _ _ this).symm

/- English proof (translation)
Establish `h` using `fun u => (hS.2.2.1 _ (inR'_Eel hS) (S.e.symm u)).symm.trans (hS.2.2.2.2.2.2.2.2.2.2.1.2.2.1 _)`. Simplify using `only [LinearEquiv.apply_symm_apply] at h`. Use `⟨mat_ext fun v => ?_, fun c hc => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]`. Conclude with `congrArg Prod.fst (h (v, 0))`.

Use `congrFun (congrArg Prod.snd (h (0, fun _ => 1))) c` as an intermediate fact. Simplify using `only [mul_one, if_neg hc] at this`. Conclude with `IsFractionRing.injective (D.nd.O i) (KK D.nd i) (this.trans (map_zero _).symm)`.
-/
theorem psi_Eel (hS : GoodCongruenceObjects D.nd r ρ π S) :
    S.ψρ (Eel D.nd S) = 0 ∧ ∀ c : Fin D.R.t, (c : ℕ) ≠ 0 → S.ψχ c (Eel D.nd S) = 0 := by
  have h := fun u => (hS.2.2.1 _ (inR'_Eel hS) (S.e.symm u)).symm.trans (hS.2.2.2.2.2.2.2.2.2.2.1.2.2.1 _)
  simp only [LinearEquiv.apply_symm_apply] at h
  refine ⟨mat_ext fun v => ?_, fun c hc => ?_⟩
  · rw [Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]
    exact congrArg Prod.fst (h (v, 0))
  · have := congrFun (congrArg Prod.snd (h (0, fun _ => 1))) c
    simp only [mul_one, if_neg hc] at this
    exact IsFractionRing.injective (D.nd.O i) (KK D.nd i) (this.trans (map_zero _).symm)

/- English proof (translation)
Establish `hp : S.p S.π' = π` using `hS.2.2.2.2.2.2.2.2.2.1.1`. Establish `hsum : ∀ {k : ℕ} (A : Fin m → Matrix (Fin k) (Fin k) (D.nd.O i)) (v : Fin k → KK D.nd i), ((∑ j, f j S.π' • A j).map (toK D.nd i)).mulVec v = ∑ j, toK D.nd i (f j S.π') • ((A j).map (toK D.nd i)).mulVec v`. Introduce `k A v`. Express the relevant statement in the definitionally equal form `((toK D.nd i).mapMatrix _).mulVec v = _`. Rewrite using `[map_sum, Matrix.sum_mulVec]`.

Conclude with `Finset.sum_congr rfl fun j _ => map_smul_mulVec _ _ _`. Establish `h1 : ∀ g u, S.e (((rO D.nd i r π g).map (toK D.nd i)).mulVec u) = (((rhoO D.nd i ρ π g).map (toK D.nd i)).mulVec (S.e u).1, fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (S.e u).2 c)` using `hS.2.1`. Establish `h` using `fun u => hS.2.2.2.2.2.2.2.2.2.2.1.2.2.1 (S.e.symm u)`. Rewrite `h` using `[congrFun e S.π']`. Simplify using `only [Finset.sum_apply, hp, hsum, map_sum, map_smul, h1, LinearEquiv.apply_symm_apply] at h`.

Use `⟨mat_ext fun v => ?_, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec, hsum]`. Use `congrArg Prod.fst (h (v, 0))` as an intermediate fact. Rewrite `this` using `[Prod.fst_sum]`. Conclude with `this`.

Use `congrFun (congrArg Prod.snd (h (0, fun _ => 1))) c` as an intermediate fact. Rewrite `this` using `[Prod.snd_sum, Finset.sum_apply]`. Simplify using `only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_one] at this`. Apply `IsFractionRing.injective (D.nd.O i) (KK D.nd i)` to reduce the goal to its premises. Rewrite using `[apply_ite (algebraMap (D.nd.O i) (KK D.nd i)), map_zero, map_sum]`.

Simplify using `only [map_mul]`. Conclude with `this`.
-/
theorem sum_blocks (hS : GoodCongruenceObjects D.nd r ρ π S)
    {m : ℕ} {f : Fin m → S.X' → D.nd.O i} {g : Fin m → GE D.nd}
    (e : Eel D.nd S = ∑ j, fun x' => f j x' • rO D.nd i r (S.p x') (g j)) :
    ∑ j, f j S.π' • rhoO D.nd i ρ π (g j) = 0 ∧
      ∀ c : Fin D.R.t, ∑ j, f j S.π' * ((chiU D.nd i ((c : ℕ) + 1) (g j) : (D.nd.O i)ˣ) : D.nd.O i) =
        if (c : ℕ) = 0 then del51 D.nd S S.π' else 0 := by
  have hp : S.p S.π' = π := hS.2.2.2.2.2.2.2.2.2.1.1
  have hsum : ∀ {k : ℕ} (A : Fin m → Matrix (Fin k) (Fin k) (D.nd.O i)) (v : Fin k → KK D.nd i),
      ((∑ j, f j S.π' • A j).map (toK D.nd i)).mulVec v =
        ∑ j, toK D.nd i (f j S.π') • ((A j).map (toK D.nd i)).mulVec v := by
    intro k A v
    change ((toK D.nd i).mapMatrix _).mulVec v = _
    rw [map_sum, Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun j _ => map_smul_mulVec _ _ _
  have h1 : ∀ g u, S.e (((rO D.nd i r π g).map (toK D.nd i)).mulVec u) =
      (((rhoO D.nd i ρ π g).map (toK D.nd i)).mulVec (S.e u).1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (S.e u).2 c) :=
    hS.2.1
  have h := fun u => hS.2.2.2.2.2.2.2.2.2.2.1.2.2.1 (S.e.symm u)
  rw [congrFun e S.π'] at h
  simp only [Finset.sum_apply, hp, hsum, map_sum, map_smul, h1, LinearEquiv.apply_symm_apply] at h
  refine ⟨mat_ext fun v => ?_, fun c => ?_⟩
  · rw [Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec, hsum]
    have := congrArg Prod.fst (h (v, 0))
    rw [Prod.fst_sum] at this
    exact this
  · have := congrFun (congrArg Prod.snd (h (0, fun _ => 1))) c
    rw [Prod.snd_sum, Finset.sum_apply] at this
    simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_one] at this
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    rw [apply_ite (algebraMap (D.nd.O i) (KK D.nd i)), map_zero, map_sum]
    simp only [map_mul]
    exact this

/- English proof (translation)
Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H v`. Simplify using `only [Check.matKO_mk]`. Express the relevant statement in the definitionally equal form `(stdG O (FractionRing O) k).mkQ _ = ∑ j, a j • (stdG O (FractionRing O) k).mkQ _`. Simplify using `only [← map_smul, ← map_sum]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `((algebraMap O (FractionRing O)).mapMatrix _).mulVec v = _`. Rewrite using `[map_sum, Matrix.sum_mulVec]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul (FractionRing O) (a j) (Matrix.mulVec _ v), ← Matrix.smul_mulVec]`.

Use `congr 1`. Use extensionality with `p q`. Simplify using the standard rewrite rules.
-/
theorem matKO_sum {O : Type} [CommRing O] [IsDomain O] {k m : ℕ} (a : Fin m → O)
    (A : Fin m → Matrix (Fin k) (Fin k) O) (x : KOG O k) :
    matKO (∑ j, a j • A j) x = ∑ j, a j • matKO (A j) x := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    simp only [Check.matKO_mk]
    change (stdG O (FractionRing O) k).mkQ _ = ∑ j, a j • (stdG O (FractionRing O) k).mkQ _
    simp only [← map_smul, ← map_sum]
    congr 1
    change ((algebraMap O (FractionRing O)).mapMatrix _).mulVec v = _
    rw [map_sum, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul (FractionRing O) (a j) (Matrix.mulVec _ v), ← Matrix.smul_mulVec]
    congr 1
    ext p q
    simp

/- English proof (translation)
Take `⟨m, f, g, hf, e⟩` from `inR'_Eel hS`. Establish `h` using `del_smul_sum hS Xs ψ hE hψ hf e hw`. Establish `h0` using `(sum_blocks hS e).2 ⟨0, D.R.t_odd.pos⟩`. Simplify using `only [zero_add, if_true, mul_comm (f _ _)] at h0`. Simplify using `only [amitsur_d0_apply, smul_sub, Finset.sum_sub_distrib, Check.WKG_eq_matKO] at h`.

Rewrite `h` using `[← matKO_sum, hM e, ← Finset.sum_smul, h0, ← zero_smul (D.nd.O i) (1 : Matrix (Fin k) (Fin k) (D.nd.O i)), Check.matKO_smul_one, zero_smul, smul_zero, zero_sub, neg_eq_zero, smul_smul]`. Conclude with `h`.
-/
theorem del_sq_smul (hS : GoodCongruenceObjects D.nd r ρ π S) (Xs : Set (D.nd.X i)) {k : ℕ}
    (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) (hE : ψ (Eel D.nd S) = 0)
    (hψ : ∀ f ∈ S.T', ψ (fun x' => f x' • (1 : MatN D.nd i)) = f S.π' • 1)
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : ∀ {m : ℕ} {f : Fin m → S.X' → D.nd.O i} {g : Fin m → GE D.nd},
      (Eel D.nd S = ∑ j, fun x' => f j x' • rO D.nd i r (S.p x') (g j)) →
      ∑ j, (((chiU D.nd i 1 (g j) : (D.nd.O i)ˣ) : D.nd.O i) * f j S.π') • M (g j) = 0)
    (w : KOG (D.nd.O i) k) (hw : d0 (WKG M) w ∈ cocW i r S Xs ψ) :
    (del51 D.nd S S.π' * del51 D.nd S S.π') • w = 0 := by
  obtain ⟨m, f, g, hf, e⟩ := inR'_Eel hS
  have h := del_smul_sum hS Xs ψ hE hψ hf e hw
  have h0 := (sum_blocks hS e).2 ⟨0, D.R.t_odd.pos⟩
  simp only [zero_add, if_true, mul_comm (f _ _)] at h0
  simp only [amitsur_d0_apply, smul_sub, Finset.sum_sub_distrib, Check.WKG_eq_matKO] at h
  rw [← matKO_sum, hM e, ← Finset.sum_smul, h0, ← zero_smul (D.nd.O i) (1 : Matrix (Fin k) (Fin k) (D.nd.O i)),
    Check.matKO_smul_one, zero_smul, smul_zero, zero_sub, neg_eq_zero, smul_smul] at h
  exact h

/- English proof (translation)
Introduce `D i r ρ π Xs S _ hS _`. Use `⟨length_inf_coboundaries_le_two_mul_rank _ _ _ (del_sq_smul hS Xs _ (psi_Eel hS).1 (fun f hf => (psi_scalar hS hf).1) _ ?_), fun c => ?_⟩` and prove the remaining obligations. Introduce `m f g e`. Rewrite using `[← (sum_blocks hS e).1]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ • ((((chiU D.nd i 1 (g j))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • rhoO D.nd i ρ π (g j)) = _`. Rewrite using `[smul_smul, mul_right_comm, Units.mul_inv, one_mul]`. Establish `hχ : ∀ g, chiRatO D.nd i ((c : ℕ) + 1) g = ((chiU D.nd i ((c : ℕ) + 1) g * (chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i))` using `fun _ => rfl`. Distinguish the cases in `hc : (c : ℕ) = 0`. Establish `: ReciprocityTheory.Gal.B1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) = ⊥`.

Rewrite using `[eq_bot_iff]`. Introduce and unpack `_ ⟨w, rfl⟩`. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `WKG _ g w - w = 0`. Rewrite using `[Check.WKG_eq_matKO, hχ, Check.matKO_smul_one, hc, zero_add, mul_inv_cancel, Units.val_one, one_smul, sub_self]`.

Rewrite using `[lenCob, this, inf_bot_eq, Module.length_bot]`. Conclude with `zero_le`. Use `length_inf_coboundaries_le_two_mul_rank _ _ _ (del_sq_smul hS Xs _ ?_ (fun f hf => ?_) _ ?_)` and prove the remaining obligations. Simplify using `only [(psi_Eel hS).2 c hc, zero_smul]`. Simplify using `only [(psi_scalar hS hf).2 c]`.

Introduce `m f g e`. Establish `h` using `(sum_blocks hS e).2 c`. Rewrite `h` using `[if_neg hc]`. Simplify using `only [hχ, smul_smul]`. Rewrite using `[← Finset.sum_smul]`.

Use `zero_smul (D.nd.O i) (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i))` and compare the differences between its conclusion and the goal. Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, mul_mul_mul_comm, mul_comm _ ((chiU D.nd i ((c : ℕ) + 1) (g j) : (D.nd.O i)ˣ) : D.nd.O i)]`. Use `(chiU D.nd i 1 (g j)).mul_inv` as an intermediate fact.

Take the linear combination `(f j S.π' * ((chiU D.nd i ((c : ℕ) + 1) (g j) : (D.nd.O i)ˣ) : D.nd.O i)) * this`.
-/
theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → lenCob i (WpO D.nd i ρ π) (cocRho i r S Xs) ≤ ((2 * D.R.r : ℕ) : ℕ∞) * lenQ i (del51 D.nd S S.π') ∧ ∀ c : Fin D.R.t, lenCob i (chiRatO D.nd i ((c : ℕ) + 1)) (cocChi i r S Xs c) ≤ 2 * lenQ i (del51 D.nd S S.π') := by
  intro D i r ρ π Xs S _ hS _
  refine ⟨length_inf_coboundaries_le_two_mul_rank _ _ _ (del_sq_smul hS Xs _ (psi_Eel hS).1 (fun f hf => (psi_scalar hS hf).1) _ ?_),
    fun c => ?_⟩
  · intro m f g e
    rw [← (sum_blocks hS e).1]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ • ((((chiU D.nd i 1 (g j))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • rhoO D.nd i ρ π (g j)) = _
    rw [smul_smul, mul_right_comm, Units.mul_inv, one_mul]
  have hχ : ∀ g, chiRatO D.nd i ((c : ℕ) + 1) g =
      ((chiU D.nd i ((c : ℕ) + 1) g * (chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
        (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := fun _ => rfl
  by_cases hc : (c : ℕ) = 0
  · have : ReciprocityTheory.Gal.B1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨w, rfl⟩
      funext g
      change WKG _ g w - w = 0
      rw [Check.WKG_eq_matKO, hχ, Check.matKO_smul_one, hc, zero_add, mul_inv_cancel, Units.val_one, one_smul,
        sub_self]
    rw [lenCob, this, inf_bot_eq, Module.length_bot]
    exact zero_le
  · refine length_inf_coboundaries_le_two_mul_rank _ _ _ (del_sq_smul hS Xs _ ?_ (fun f hf => ?_) _ ?_)
    · simp only [(psi_Eel hS).2 c hc, zero_smul]
    · simp only [(psi_scalar hS hf).2 c]
    · intro m f g e
      have h := (sum_blocks hS e).2 c
      rw [if_neg hc] at h
      simp only [hχ, smul_smul]
      rw [← Finset.sum_smul]
      convert zero_smul (D.nd.O i) (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i))
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Units.val_mul, mul_mul_mul_comm, mul_comm _ ((chiU D.nd i ((c : ℕ) + 1) (g j) : (D.nd.O i)ˣ) : D.nd.O i)]
      have := (chiU D.nd i 1 (g j)).mul_inv
      linear_combination (f j S.π' * ((chiU D.nd i ((c : ℕ) + 1) (g j) : (D.nd.O i)ˣ) : D.nd.O i)) * this

end GlobalTheory.Cut.Cob
