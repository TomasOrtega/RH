import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.CMemPolyT
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.Normal
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.BurnsideMat
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SpacedProductLowerBound

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

section Blocks
variable {A : Type*} [CommRing A] {d : Type} [Fintype d] [DecidableEq d] {α : Type} [DecidableEq α]
  (bl : d → α)

/- English proof (translation)
Use extensionality with `⟨i, hi⟩ ⟨j, hj⟩`. Simplify using `only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.mul_apply]`. Establish `h0 : ∑ k : {k // ¬ bl k = c}, M i (k : d) * N (k : d) j = 0`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hM i k (by rw [hi]; exact Ne.symm k.2), zero_mul]`.

Rewrite using `[← Fintype.sum_subtype_add_sum_subtype (fun k => bl k = c) (fun k => M i k * N k j), h0, add_zero]`.
-/
theorem blk_mul {M N : Matrix d d A} (hM : ∀ i j, bl i ≠ bl j → M i j = 0) (c : α) :
    (M * N).toSquareBlock bl c = M.toSquareBlock bl c * N.toSquareBlock bl c := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.mul_apply]
  have h0 : ∑ k : {k // ¬ bl k = c}, M i (k : d) * N (k : d) j = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hM i k (by rw [hi]; exact Ne.symm k.2), zero_mul]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => bl k = c) (fun k => M i k * N k j), h0,
    add_zero]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Introduce `k _ hk`. Rewrite using `[hM i k (fun h => hk (hi k h).symm), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem diag_mul {M N : Matrix d d A} (hM : ∀ i j, bl i ≠ bl j → M i j = 0) (i : d)
    (hi : ∀ l, bl i = bl l → i = l) : (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rw [hM i k (fun h => hk (hi k h).symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

end Blocks

/- English proof (translation)
Use `⟨{g}, fun _ => 1, fun _ => T.one_mem, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.
-/
theorem r_mem {O : Type} [CommRing O] {X : Type} (T : Subalgebra O (X → O)) {d : Type} [Fintype d]
    [DecidableEq d] {G : Type} [Monoid G] (r : G →* (X → Matrix d d O)) (g : G) : r g ∈ tSpan T r := by
  refine ⟨{g}, fun _ => 1, fun _ => T.one_mem, ?_⟩
  funext x
  simp

/- English proof (translation)
Rewrite using `[Matrix.rank_diagonal, Nat.card_eq_fintype_card]`. Apply the tactic sequence `exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => by by_cases h : S a <;> simp [h])`.
-/
theorem rank_diag_ite {K : Type*} [Field K] {d : Type} [Fintype d] [DecidableEq d] (S : d → Prop)
    [DecidablePred S] :
    (Matrix.diagonal fun a => if S a then (1 : K) else 0).rank = Nat.card {a // S a} := by
  rw [Matrix.rank_diagonal, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => by by_cases h : S a <;> simp [h])

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `O _ _ _ _ X _ T d _ _ G _ r π t bl χ₁ ε hP hirr hcard0`. Take `⟨hloc, hpts, hG1, hbd, hc1, hχ⟩` from `hP`. Set `R` to `spanSub T r`. Set `k` to `IsLocalRing.ResidueField O`. Set `res : O →+* k` to `IsLocalRing.residue O`.

Establish `huniq : ∀ a b : d, bl a ≠ 0 → bl a = bl b → a = b`. Introduce `a b ha hab`. Establish `hs : Subsingleton {x // bl x = bl a}` using `Fintype.card_le_one_iff_subsingleton.mp (le_of_eq (hc1 _ ha))`. Conclude with `congrArg Subtype.val (hs.elim ⟨a, rfl⟩ ⟨b, hab.symm⟩)`. Establish `hBD : ∀ a ∈ tSpan T r, ∀ i j, bl i ≠ bl j → a π i j = 0`.

Introduce and unpack `a ⟨s, c, hc, rfl⟩ i j hij`. Simplify using `[Finset.sum_apply, Matrix.sum_apply, hbd _ i j hij]`. Set `n0` to `{a // bl a = 0}`. Set `ι` to `{a // bl a ≠ 0}`. Set `Φ : R →+* Matrix n0 n0 O × (ι → O)` to `{ toFun := fun a => ((a.1 π).toSquareBlock bl 0, fun i => a.1 π i.1 i.1) map_one' := by`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[Matrix.toSquareBlock_def]`.

Establish `h' : i.1 ≠ j.1` using `fun e => h (Subtype.ext e)`. Simplify using `[Matrix.toSquareBlock_def, Matrix.one_apply, h, h']`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Use the proof step `map_mul' := fun a b => Prod.ext (blk_mul bl (hBD a.1 a.2) 0) (funext fun i => diag_mul bl (hBD a.1 a.2) i.1 (fun l hl => huniq _ _ i.2 hl))`.

Use the proof step `map_zero' := by`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `[Matrix.toSquareBlock_def]`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Use the proof step `map_add' := fun a b => by`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `[Matrix.toSquareBlock_def]`.

Use function extensionality and compare the values at `i`. Simplify using `}`. Set `f₀ : R →+* Matrix n0 n0 k × (ι → k)` to `(RingHom.prodMap res.mapMatrix (RingHom.compLeft res ι)).comp Φ`. Establish `hf1 : ∀ (a : R) i j, (f₀ a).1 i j = res (a.1 π i.1 j.1)` using `fun a i j => rfl`. Establish `hf2 : ∀ (a : R) i, (f₀ a).2 i = res (a.1 π i.1 i.1)` using `fun a i => rfl`.

Establish `hsm : ∀ (c : O) (a : R), f₀ (c • a) = res c • f₀ a`. Introduce `c a`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use extensionality with `i j`. Rewrite using `[hf1]`.

Simplify using `[hf1]`. Use function extensionality and compare the values at `i`. Rewrite using `[hf2]`. Simplify using `[hf2]`. Set `B' : Subalgebra k (Matrix n0 n0 k × (ι → k))` to `{ toSubsemiring := f₀.rangeS algebraMap_mem' := fun c => by`.

Take `⟨c0, rfl⟩` from `IsLocalRing.residue_surjective c`. Use `⟨c0 • (1 : R), ?_⟩` and prove the remaining obligations. Rewrite using `[hsm, map_one, Algebra.algebraMap_eq_smul_one] }`. Establish `hB' : ∀ z, z ∈ B' ↔ ∃ a, f₀ a = z` using `fun z => Iff.rfl`. Take `⟨i0⟩ : Nonempty n0` from `Fintype.card_pos_iff.mp (lt_of_lt_of_le (by norm_num) hcard0)`.

Establish `: Nonempty n0` using `⟨i0⟩`. Set `rR : G →* R` to `{ toFun := fun g => ⟨r g, r_mem T r g⟩ map_one' := Subtype.ext (map_one r) map_mul' := fun g h => Subtype.ext (map_mul r g h) }`. Set `ρb : G →* Matrix n0 n0 k` to `(((RingHom.fst _ _).comp f₀).toMonoidHom).comp rR`. Establish `hb : Submodule.span k (Set.range ρb) = ⊤` using `burnsideMat k n0 G ρb hirr`. Establish `hsurj : ∀ A : Matrix n0 n0 k, ∃ z ∈ B', z.1 = A`.

Introduce `A`. Establish `hA : A ∈ Submodule.span k (Set.range ρb)` using `hb ▸ Submodule.mem_top`. Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨g, rfl⟩` from `hx`.

Conclude with `⟨f₀ (rR g), ⟨rR g, rfl⟩, rfl⟩`. Consider the case `zero => exact ⟨0, B'.zero_mem, rfl⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨b, hb', rfl⟩` from `hy`.

Conclude with `⟨a + b, B'.add_mem ha hb', rfl⟩`. Consider the case `smul c x _ hx`. Take `⟨a, ha, rfl⟩` from `hx`. Conclude with `⟨c • a, B'.smul_mem ha c, rfl⟩`. Establish `hcor` using `cornerIdem k n0 ι B' hcard0 hsurj`.

Take `⟨u1, hu1⟩` from `(hB' _).mp (hcor 1)`. Take `⟨u2, hu2⟩` from `(hB' _).mp (hcor (Matrix.single i0 i0 1))`. Establish `hv1 : f₀ (1 - u1) = (0, 1)`. Rewrite using `[map_sub, map_one, hu1]`. Apply the tactic sequence `refine Prod.ext ?_ ?_ <;> simp`.

Establish `hfin : Module.Finite O R` using `(inferInstance : Module.Finite O (Subalgebra.toSubmodule R))`. Set `f` to `f₀.rangeRestrict`. Establish `hfs : Function.Surjective f` using `f₀.rangeRestrict_surjective`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}` using `hϖ.maximalIdeal_eq`.

Take `⟨N, hN⟩` from `satur O (X → Matrix d d O) (Subalgebra.toSubmodule R)`. Establish `h5 : ∀ a ∈ IsLocalRing.maximalIdeal O • Subalgebra.toSubmodule R, ∃ w : R, w ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O R) ∧ w.1 = a`. Introduce `a ha`. Proceed by induction on `ha using Submodule.smul_induction_on' with`. Consider the case `smul c hc m hm => exact ⟨c • ⟨m, hm⟩, Submodule.smul_mem_smul hc Submodule.mem_top, rfl⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨w, hw, rfl⟩` from `ha`. Take `⟨w', hw', rfl⟩` from `hb`. Conclude with `⟨w + w', Submodule.add_mem _ hw hw', rfl⟩`. Establish `hker : ∀ x : R, f x = 0 → ∃ n : ℕ, x ^ n ∈ (IsLocalRing.maximalIdeal O) • (⊤ : Submodule O R)`.

Introduce `x hx`. Establish `hx0 : f₀ x = 0` using `congrArg Subtype.val hx`. Establish `hπ : (x.1 π).map res = 0`. Use extensionality with `i j`. Distinguish the cases in `hij : bl i = bl j`.

Distinguish the cases in `hi : bl i = 0`. Conclude with `congrFun (congrFun (congrArg Prod.fst hx0) ⟨i, hi⟩) ⟨j, hij ▸ hi⟩`. Establish `hh` using `huniq i j hi hij`. Substitute `hh` using the available equality. Conclude with `congrFun (congrArg Prod.snd hx0) ⟨i, hi⟩`.

Simplify using `[hBD x.1 x.2 i j hij]`. Establish `hnil` using `nilConst O X T d hloc x.1 (charT O X T d G r hG1 x.1 x.2) π hπ`. Establish `hdiv : ∀ y i j, ∃ c, ((x.1 y) ^ Fintype.card d) i j = ϖ * c`. Introduce `y i j`. Establish `h1 : res (((x.1 y) ^ Fintype.card d) i j) = 0` using `congrFun (congrFun (hnil y) i) j`.

Establish `h2 : ((x.1 y) ^ Fintype.card d) i j ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.residue_eq_zero_iff _).mp h1`. Rewrite `h2` using `[hmax, Ideal.mem_span_singleton]`. Conclude with `h2`. Use `choose c hc using hdiv`. Set `y : X → Matrix d d O` to `fun z => Matrix.of (c z)`.

Establish `hxy : x.1 ^ Fintype.card d = ϖ • y`. Use function extensionality and compare the values at `z`. Use extensionality with `i j`. Simplify using `[y, hc]`. Use `⟨Fintype.card d * N, ?_⟩` and prove the remaining obligations.

Establish `h3 : x.1 ^ (Fintype.card d * N) ∈ (IsLocalRing.maximalIdeal O) ^ N • (⊤ : Submodule O (X → Matrix d d O))`. Rewrite using `[pow_mul, hxy, smul_pow]`. Conclude with `Submodule.smul_mem_smul (Ideal.pow_mem_pow (hmax ▸ Ideal.mem_span_singleton_self ϖ) N) Submodule.mem_top`. Take `⟨w, hw, hwe⟩` from `h5 _ (hN (x.1 ^ (Fintype.card d * N)) (R.pow_mem x.2 _) h3)`. Establish `hwx : w = x ^ (Fintype.card d * N)` using `Subtype.ext hwe`.

Rewrite using `[← hwx]`. Conclude with `hw`. Establish `hi1 : IsIdempotentElem (f (1 - u1))` using `Subtype.ext (by show f₀ (1 - u1) * f₀ (1 - u1) = f₀ (1 - u1)`. Apply the tactic sequence `rw [hv1]; refine Prod.ext ?_ ?_ <;> simp)`. Establish `hi2 : IsIdempotentElem (f u2)` using `Subtype.ext (by show f₀ u2 * f₀ u2 = f₀ u2`.

Apply the tactic sequence `rw [hu2]; refine Prod.ext ?_ ?_ <;> simp)`. Establish `h12 : f (1 - u1) * f u2 = 0` using `Subtype.ext (by show f₀ (1 - u1) * f₀ u2 = 0`. Apply the tactic sequence `rw [hv1, hu2]; refine Prod.ext ?_ ?_ <;> simp)`. Establish `h21 : f u2 * f (1 - u1) = 0` using `Subtype.ext (by show f₀ u2 * f₀ (1 - u1) = 0`. Apply the tactic sequence `rw [hv1, hu2]; refine Prod.ext ?_ ?_ <;> simp)`.

Take `⟨E₁, E₂, hE1, hE2, hE12, hE21, hfE1, hfE2⟩` from `idemLift O R f₀.range f hfs hker _ _ hi1 hi2 h12 h21`. Establish `hg1 : f₀ E₁ = (0, 1)` using `(congrArg Subtype.val hfE1).trans hv1`. Establish `hg2 : f₀ E₂ = (Matrix.single i0 i0 1, 0)` using `(congrArg Subtype.val hfE2).trans hu2`. Establish `hΦ1 : Φ E₁ * Φ E₁ = Φ E₁` using `by rw [← map_mul, hE1.eq]`. Establish `hΦ2 : Φ E₂ * Φ E₂ = Φ E₂` using `by rw [← map_mul, hE2.eq]`.

Establish `hb1 : (Φ E₁).1 = 0` using `idemSmall O n0 (Φ E₁).1 (congrArg Prod.fst hΦ1) (congrArg Prod.fst hg1)`. Establish `hd1 : ∀ i : ι, E₁.1 π i.1 i.1 = 1`. Introduce `i`. Establish `h1 : IsIdempotentElem (E₁.1 π i.1 i.1)` using `congrFun (congrArg Prod.snd hΦ1) i`. Establish `h2 : res (E₁.1 π i.1 i.1) = 1` using `congrFun (congrArg Prod.snd hg1) i`.

Break down `IsIdempotentElem.iff_eq_zero_or_one.mp h1 with h | h` into its components or cases. Rewrite `h2` using `[h, map_zero]`. Conclude with `absurd h2 zero_ne_one`. Conclude with `h`. Establish `hd2 : ∀ i : ι, E₂.1 π i.1 i.1 = 0`.

Introduce `i`. Establish `h1 : IsIdempotentElem (E₂.1 π i.1 i.1)` using `congrFun (congrArg Prod.snd hΦ2) i`. Establish `h2 : res (E₂.1 π i.1 i.1) = 0` using `congrFun (congrArg Prod.snd hg2) i`. Break down `IsIdempotentElem.iff_eq_zero_or_one.mp h1 with h | h` into its components or cases. Conclude with `h`.

Rewrite `h2` using `[h, map_one]`. Conclude with `absurd h2 one_ne_zero`. Establish `heB : E₁.1 π = Matrix.diagonal (fun a => if bl a = 0 then 0 else 1)`. Use extensionality with `i j`. Distinguish the cases in `hij : bl i = bl j`.

Distinguish the cases in `hi : bl i = 0`. Establish `h1 : E₁.1 π i j = 0` using `congrFun (congrFun hb1 ⟨i, hi⟩) ⟨j, hij ▸ hi⟩`. Rewrite using `[h1]`. Distinguish the cases in `hh : i = j`. Substitute `hh` using the available equality.

Simplify using `[hi]`. Rewrite using `[Matrix.diagonal_apply_ne _ hh]`. Establish `hh` using `huniq i j hi hij`. Substitute `hh` using the available equality. Rewrite using `[hd1 ⟨i, hi⟩]`.

Simplify using `[hi]`. Rewrite using `[hBD E₁.1 E₁.2 i j hij, Matrix.diagonal_apply_ne _ (fun h => hij (congrArg bl h))]`. Establish `he1 : ∀ a b, (bl a ≠ 0 ∨ bl b ≠ 0) → E₂.1 π a b = 0`. Introduce `a b hab`. Distinguish the cases in `hij : bl a = bl b`.

Establish `ha : bl a ≠ 0`. Break down `hab with h | h` into its components or cases. Conclude with `h`. Rewrite using `[hij]`. Conclude with `h`.

Establish `hh` using `huniq a b ha hij`. Substitute `hh` using the available equality. Conclude with `hd2 ⟨a, ha⟩`. Conclude with `hBD E₂.1 E₂.2 a b hij`. Establish `hcardι : Fintype.card {a // bl a ≠ 0} = t`.

Establish `hbij : Function.Bijective (fun a : {a // bl a ≠ 0} => (⟨bl a.1, a.2⟩ : {c : Fin (t + 1) // c ≠ 0}))`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Conclude with `Subtype.ext (huniq a.1 b.1 a.2 (congrArg Subtype.val hab))`. Introduce `c`.

Take `⟨a⟩ : Nonempty {a // bl a = c.1}` from `Fintype.card_pos_iff.mp (by rw [hc1 c.1 c.2]; norm_num)`. Conclude with `⟨⟨a.1, by rw [a.2]; exact c.2⟩, Subtype.ext a.2⟩`. Rewrite using `[Fintype.card_of_bijective hbij]`. Simplify using `[Fintype.card_subtype_compl]`. Establish `hrB : ((E₁.1 π).map (algebraMap O (FractionRing O))).rank = t`.

Establish `h1 : (E₁.1 π).map (algebraMap O (FractionRing O)) = Matrix.diagonal fun a => if bl a ≠ 0 then (1 : FractionRing O) else 0`. Rewrite using `[heB]`. Use extensionality with `i j`. Distinguish the cases in `hh : i = j`. Substitute `hh` using the available equality.

Apply the tactic sequence `by_cases hi : bl i = 0 <;> simp [hi]`. Simplify using `[Matrix.diagonal_apply_ne _ hh]`. Rewrite using `[h1, rank_diag_ite, Nat.card_eq_fintype_card]`. Use `hcardι` and compare the differences between its conclusion and the goal. Establish `hr1 : ((E₂.1 π).map (algebraMap O (FractionRing O))).rank = 1`.

Rewrite using `[← rankMod O d (E₂.1 π) (congrFun (congrArg Subtype.val hE2.eq) π)]`. Establish `h1 : (E₂.1 π).map (IsLocalRing.residue O) = Matrix.diagonal fun a => if a = i0.1 then (1 : k) else 0`. Use extensionality with `i j`. Distinguish the cases in `hi : bl i = 0 ∧ bl j = 0`. Establish `h2 : res (E₂.1 π i j) = Matrix.single i0 i0 (1 : k) ⟨i, hi.1⟩ ⟨j, hi.2⟩` using `congrFun (congrFun (congrArg Prod.fst hg2) ⟨i, hi.1⟩) ⟨j, hi.2⟩ show res (E₂.1 π i j) = _`.

Rewrite using `[h2, Matrix.single_apply, Matrix.diagonal_apply]`. Distinguish the cases in `h3 : i = i0.1`. Distinguish the cases in `h4 : j = i0.1`. Substitute `h3` using the available equality. Substitute `h4` using the available equality.

Simplify using the standard rewrite rules. Establish `: ¬ (i0 = ⟨j, hi.2⟩)` using `fun e => h4 (congrArg Subtype.val e).symm`. Establish `h5 : i ≠ j` using `fun e => h4 (e ▸ h3)`. Simplify using `[this, h5]`. Establish `: ¬ (i0 = ⟨i, hi.1⟩)` using `fun e => h3 (congrArg Subtype.val e).symm`.

Simplify using `[this, h3]`. Establish `h2 : E₂.1 π i j = 0` using `he1 i j (by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hi hcon)`.

Use `show res (E₂.1 π i j) = _`. Rewrite using `[h2, map_zero, Matrix.diagonal_apply]`. Distinguish the cases in `h3 : i = j`. Substitute `h3` using the available equality. Establish `: i ≠ i0.1` using `fun e => hi ⟨e ▸ i0.2, e ▸ i0.2⟩`.

Simplify using `[this]`. Simplify using `[h3]`. Rewrite using `[h1, rank_diag_ite, Nat.card_eq_fintype_card]`. Simplify using the standard rewrite rules. Use `⟨E₁.1, E₂.1, E₁.2, E₂.2, congrArg Subtype.val hE1.eq, congrArg Subtype.val hE2.eq, congrArg Subtype.val hE12, congrArg Subtype.val hE21, fun x => ?_, fun x => ?_, heB, he1⟩` and prove the remaining obligations.

Rewrite using `[rankConst O X T d hloc E₁.1 (congrArg Subtype.val hE1.eq) (charT O X T d G r hG1 E₁.1 E₁.2) x π, hrB]`. Rewrite using `[rankConst O X T d hloc E₂.1 (congrArg Subtype.val hE2.eq) (charT O X T d G r hG1 E₂.1 E₂.2) x π, hr1]`.
-/
theorem idem : StatIdem := by
  intro O _ _ _ _ X _ T d _ _ G _ r π t bl χ₁ ε hP hirr hcard0
  obtain ⟨hloc, hpts, hG1, hbd, hc1, hχ⟩ := hP
  let R := spanSub T r
  let k := IsLocalRing.ResidueField O
  let res : O →+* k := IsLocalRing.residue O
  have huniq : ∀ a b : d, bl a ≠ 0 → bl a = bl b → a = b := by
    intro a b ha hab
    have hs : Subsingleton {x // bl x = bl a} :=
      Fintype.card_le_one_iff_subsingleton.mp (le_of_eq (hc1 _ ha))
    exact congrArg Subtype.val (hs.elim ⟨a, rfl⟩ ⟨b, hab.symm⟩)
  have hBD : ∀ a ∈ tSpan T r, ∀ i j, bl i ≠ bl j → a π i j = 0 := by
    rintro a ⟨s, c, hc, rfl⟩ i j hij
    simp [Finset.sum_apply, Matrix.sum_apply, hbd _ i j hij]
  let n0 := {a // bl a = 0}
  let ι := {a // bl a ≠ 0}
  let Φ : R →+* Matrix n0 n0 O × (ι → O) :=
    { toFun := fun a => ((a.1 π).toSquareBlock bl 0, fun i => a.1 π i.1 i.1)
      map_one' := by
        refine Prod.ext ?_ ?_
        · ext i j
          by_cases h : i = j
          · subst h; simp [Matrix.toSquareBlock_def]
          · have h' : i.1 ≠ j.1 := fun e => h (Subtype.ext e)
            simp [Matrix.toSquareBlock_def, Matrix.one_apply, h, h']
        · funext i
          simp
      map_mul' := fun a b => Prod.ext (blk_mul bl (hBD a.1 a.2) 0)
        (funext fun i => diag_mul bl (hBD a.1 a.2) i.1 (fun l hl => huniq _ _ i.2 hl))
      map_zero' := by
        refine Prod.ext ?_ ?_
        · ext i j; simp [Matrix.toSquareBlock_def]
        · funext i; simp
      map_add' := fun a b => by
        refine Prod.ext ?_ ?_
        · ext i j; simp [Matrix.toSquareBlock_def]
        · funext i; simp }
  let f₀ : R →+* Matrix n0 n0 k × (ι → k) :=
    (RingHom.prodMap res.mapMatrix (RingHom.compLeft res ι)).comp Φ
  have hf1 : ∀ (a : R) i j, (f₀ a).1 i j = res (a.1 π i.1 j.1) := fun a i j => rfl
  have hf2 : ∀ (a : R) i, (f₀ a).2 i = res (a.1 π i.1 i.1) := fun a i => rfl
  have hsm : ∀ (c : O) (a : R), f₀ (c • a) = res c • f₀ a := by
    intro c a
    refine Prod.ext ?_ ?_
    · ext i j
      rw [hf1]
      simp [hf1]
    · funext i
      rw [hf2]
      simp [hf2]
  let B' : Subalgebra k (Matrix n0 n0 k × (ι → k)) :=
    { toSubsemiring := f₀.rangeS
      algebraMap_mem' := fun c => by
        obtain ⟨c0, rfl⟩ := IsLocalRing.residue_surjective c
        refine ⟨c0 • (1 : R), ?_⟩
        rw [hsm, map_one, Algebra.algebraMap_eq_smul_one] }
  have hB' : ∀ z, z ∈ B' ↔ ∃ a, f₀ a = z := fun z => Iff.rfl
  obtain ⟨i0⟩ : Nonempty n0 := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by norm_num) hcard0)
  have : Nonempty n0 := ⟨i0⟩
  let rR : G →* R :=
    { toFun := fun g => ⟨r g, r_mem T r g⟩
      map_one' := Subtype.ext (map_one r)
      map_mul' := fun g h => Subtype.ext (map_mul r g h) }
  let ρb : G →* Matrix n0 n0 k := (((RingHom.fst _ _).comp f₀).toMonoidHom).comp rR
  have hb : Submodule.span k (Set.range ρb) = ⊤ := burnsideMat k n0 G ρb hirr
  have hsurj : ∀ A : Matrix n0 n0 k, ∃ z ∈ B', z.1 = A := by
    intro A
    have hA : A ∈ Submodule.span k (Set.range ρb) := hb ▸ Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨f₀ (rR g), ⟨rR g, rfl⟩, rfl⟩
    | zero => exact ⟨0, B'.zero_mem, rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb', rfl⟩ := hy
      exact ⟨a + b, B'.add_mem ha hb', rfl⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨c • a, B'.smul_mem ha c, rfl⟩
  have hcor := cornerIdem k n0 ι B' hcard0 hsurj
  obtain ⟨u1, hu1⟩ := (hB' _).mp (hcor 1)
  obtain ⟨u2, hu2⟩ := (hB' _).mp (hcor (Matrix.single i0 i0 1))
  have hv1 : f₀ (1 - u1) = (0, 1) := by
    rw [map_sub, map_one, hu1]
    refine Prod.ext ?_ ?_ <;> simp
  have hfin : Module.Finite O R :=
    (inferInstance : Module.Finite O (Subalgebra.toSubmodule R))
  let f := f₀.rangeRestrict
  have hfs : Function.Surjective f := f₀.rangeRestrict_surjective
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  obtain ⟨N, hN⟩ := satur O (X → Matrix d d O) (Subalgebra.toSubmodule R)
  have h5 : ∀ a ∈ IsLocalRing.maximalIdeal O • Subalgebra.toSubmodule R,
      ∃ w : R, w ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O R) ∧ w.1 = a := by
    intro a ha
    induction ha using Submodule.smul_induction_on' with
    | smul c hc m hm => exact ⟨c • ⟨m, hm⟩, Submodule.smul_mem_smul hc Submodule.mem_top, rfl⟩
    | add a b _ _ ha hb =>
      obtain ⟨w, hw, rfl⟩ := ha
      obtain ⟨w', hw', rfl⟩ := hb
      exact ⟨w + w', Submodule.add_mem _ hw hw', rfl⟩
  have hker : ∀ x : R, f x = 0 →
      ∃ n : ℕ, x ^ n ∈ (IsLocalRing.maximalIdeal O) • (⊤ : Submodule O R) := by
    intro x hx
    have hx0 : f₀ x = 0 := congrArg Subtype.val hx
    have hπ : (x.1 π).map res = 0 := by
      ext i j
      by_cases hij : bl i = bl j
      · by_cases hi : bl i = 0
        · exact congrFun (congrFun (congrArg Prod.fst hx0) ⟨i, hi⟩) ⟨j, hij ▸ hi⟩
        · have hh := huniq i j hi hij
          subst hh
          exact congrFun (congrArg Prod.snd hx0) ⟨i, hi⟩
      · simp [hBD x.1 x.2 i j hij]
    have hnil := nilConst O X T d hloc x.1 (charT O X T d G r hG1 x.1 x.2) π hπ
    have hdiv : ∀ y i j, ∃ c, ((x.1 y) ^ Fintype.card d) i j = ϖ * c := by
      intro y i j
      have h1 : res (((x.1 y) ^ Fintype.card d) i j) = 0 := congrFun (congrFun (hnil y) i) j
      have h2 : ((x.1 y) ^ Fintype.card d) i j ∈ IsLocalRing.maximalIdeal O :=
        (IsLocalRing.residue_eq_zero_iff _).mp h1
      rw [hmax, Ideal.mem_span_singleton] at h2
      exact h2
    choose c hc using hdiv
    let y : X → Matrix d d O := fun z => Matrix.of (c z)
    have hxy : x.1 ^ Fintype.card d = ϖ • y := by
      funext z; ext i j
      simp [y, hc]
    refine ⟨Fintype.card d * N, ?_⟩
    have h3 : x.1 ^ (Fintype.card d * N) ∈
        (IsLocalRing.maximalIdeal O) ^ N • (⊤ : Submodule O (X → Matrix d d O)) := by
      rw [pow_mul, hxy, smul_pow]
      exact Submodule.smul_mem_smul
        (Ideal.pow_mem_pow (hmax ▸ Ideal.mem_span_singleton_self ϖ) N) Submodule.mem_top
    obtain ⟨w, hw, hwe⟩ := h5 _ (hN (x.1 ^ (Fintype.card d * N)) (R.pow_mem x.2 _) h3)
    have hwx : w = x ^ (Fintype.card d * N) := Subtype.ext hwe
    rw [← hwx]; exact hw
  have hi1 : IsIdempotentElem (f (1 - u1)) := Subtype.ext (by
    show f₀ (1 - u1) * f₀ (1 - u1) = f₀ (1 - u1)
    rw [hv1]; refine Prod.ext ?_ ?_ <;> simp)
  have hi2 : IsIdempotentElem (f u2) := Subtype.ext (by
    show f₀ u2 * f₀ u2 = f₀ u2
    rw [hu2]; refine Prod.ext ?_ ?_ <;> simp)
  have h12 : f (1 - u1) * f u2 = 0 := Subtype.ext (by
    show f₀ (1 - u1) * f₀ u2 = 0
    rw [hv1, hu2]; refine Prod.ext ?_ ?_ <;> simp)
  have h21 : f u2 * f (1 - u1) = 0 := Subtype.ext (by
    show f₀ u2 * f₀ (1 - u1) = 0
    rw [hv1, hu2]; refine Prod.ext ?_ ?_ <;> simp)
  obtain ⟨E₁, E₂, hE1, hE2, hE12, hE21, hfE1, hfE2⟩ :=
    idemLift O R f₀.range f hfs hker _ _ hi1 hi2 h12 h21
  have hg1 : f₀ E₁ = (0, 1) := (congrArg Subtype.val hfE1).trans hv1
  have hg2 : f₀ E₂ = (Matrix.single i0 i0 1, 0) := (congrArg Subtype.val hfE2).trans hu2
  have hΦ1 : Φ E₁ * Φ E₁ = Φ E₁ := by rw [← map_mul, hE1.eq]
  have hΦ2 : Φ E₂ * Φ E₂ = Φ E₂ := by rw [← map_mul, hE2.eq]
  have hb1 : (Φ E₁).1 = 0 :=
    idemSmall O n0 (Φ E₁).1 (congrArg Prod.fst hΦ1) (congrArg Prod.fst hg1)
  have hd1 : ∀ i : ι, E₁.1 π i.1 i.1 = 1 := by
    intro i
    have h1 : IsIdempotentElem (E₁.1 π i.1 i.1) := congrFun (congrArg Prod.snd hΦ1) i
    have h2 : res (E₁.1 π i.1 i.1) = 1 := congrFun (congrArg Prod.snd hg1) i
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp h1 with h | h
    · rw [h, map_zero] at h2; exact absurd h2 zero_ne_one
    · exact h
  have hd2 : ∀ i : ι, E₂.1 π i.1 i.1 = 0 := by
    intro i
    have h1 : IsIdempotentElem (E₂.1 π i.1 i.1) := congrFun (congrArg Prod.snd hΦ2) i
    have h2 : res (E₂.1 π i.1 i.1) = 0 := congrFun (congrArg Prod.snd hg2) i
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp h1 with h | h
    · exact h
    · rw [h, map_one] at h2; exact absurd h2 one_ne_zero
  have heB : E₁.1 π = Matrix.diagonal (fun a => if bl a = 0 then 0 else 1) := by
    ext i j
    by_cases hij : bl i = bl j
    · by_cases hi : bl i = 0
      · have h1 : E₁.1 π i j = 0 := congrFun (congrFun hb1 ⟨i, hi⟩) ⟨j, hij ▸ hi⟩
        rw [h1]
        by_cases hh : i = j
        · subst hh; simp [hi]
        · rw [Matrix.diagonal_apply_ne _ hh]
      · have hh := huniq i j hi hij
        subst hh
        rw [hd1 ⟨i, hi⟩]; simp [hi]
    · rw [hBD E₁.1 E₁.2 i j hij, Matrix.diagonal_apply_ne _ (fun h => hij (congrArg bl h))]
  have he1 : ∀ a b, (bl a ≠ 0 ∨ bl b ≠ 0) → E₂.1 π a b = 0 := by
    intro a b hab
    by_cases hij : bl a = bl b
    · have ha : bl a ≠ 0 := by
        rcases hab with h | h
        · exact h
        · rw [hij]; exact h
      have hh := huniq a b ha hij
      subst hh
      exact hd2 ⟨a, ha⟩
    · exact hBD E₂.1 E₂.2 a b hij
  have hcardι : Fintype.card {a // bl a ≠ 0} = t := by
    have hbij : Function.Bijective
        (fun a : {a // bl a ≠ 0} => (⟨bl a.1, a.2⟩ : {c : Fin (t + 1) // c ≠ 0})) := by
      constructor
      · intro a b hab
        exact Subtype.ext (huniq a.1 b.1 a.2 (congrArg Subtype.val hab))
      · intro c
        obtain ⟨a⟩ : Nonempty {a // bl a = c.1} :=
          Fintype.card_pos_iff.mp (by rw [hc1 c.1 c.2]; norm_num)
        exact ⟨⟨a.1, by rw [a.2]; exact c.2⟩, Subtype.ext a.2⟩
    rw [Fintype.card_of_bijective hbij]
    simp [Fintype.card_subtype_compl]
  have hrB : ((E₁.1 π).map (algebraMap O (FractionRing O))).rank = t := by
    have h1 : (E₁.1 π).map (algebraMap O (FractionRing O)) =
        Matrix.diagonal fun a => if bl a ≠ 0 then (1 : FractionRing O) else 0 := by
      rw [heB]
      ext i j
      by_cases hh : i = j
      · subst hh
        by_cases hi : bl i = 0 <;> simp [hi]
      · simp [Matrix.diagonal_apply_ne _ hh]
    rw [h1, rank_diag_ite, Nat.card_eq_fintype_card]
    convert hcardι
  have hr1 : ((E₂.1 π).map (algebraMap O (FractionRing O))).rank = 1 := by
    rw [← rankMod O d (E₂.1 π) (congrFun (congrArg Subtype.val hE2.eq) π)]
    have h1 : (E₂.1 π).map (IsLocalRing.residue O) =
        Matrix.diagonal fun a => if a = i0.1 then (1 : k) else 0 := by
      ext i j
      by_cases hi : bl i = 0 ∧ bl j = 0
      · have h2 : res (E₂.1 π i j) = Matrix.single i0 i0 (1 : k) ⟨i, hi.1⟩ ⟨j, hi.2⟩ :=
          congrFun (congrFun (congrArg Prod.fst hg2) ⟨i, hi.1⟩) ⟨j, hi.2⟩
        show res (E₂.1 π i j) = _
        rw [h2, Matrix.single_apply, Matrix.diagonal_apply]
        by_cases h3 : i = i0.1
        · by_cases h4 : j = i0.1
          · subst h3; subst h4; simp
          · have : ¬ (i0 = ⟨j, hi.2⟩) := fun e => h4 (congrArg Subtype.val e).symm
            have h5 : i ≠ j := fun e => h4 (e ▸ h3)
            simp [this, h5]
        · have : ¬ (i0 = ⟨i, hi.1⟩) := fun e => h3 (congrArg Subtype.val e).symm
          simp [this, h3]
      · have h2 : E₂.1 π i j = 0 := he1 i j (by
          by_contra hcon
          push Not at hcon
          exact hi hcon)
        show res (E₂.1 π i j) = _
        rw [h2, map_zero, Matrix.diagonal_apply]
        by_cases h3 : i = j
        · subst h3
          have : i ≠ i0.1 := fun e => hi ⟨e ▸ i0.2, e ▸ i0.2⟩
          simp [this]
        · simp [h3]
    rw [h1, rank_diag_ite, Nat.card_eq_fintype_card]
    simp
  refine ⟨E₁.1, E₂.1, E₁.2, E₂.2, congrArg Subtype.val hE1.eq, congrArg Subtype.val hE2.eq,
    congrArg Subtype.val hE12, congrArg Subtype.val hE21, fun x => ?_, fun x => ?_, heB, he1⟩
  · rw [rankConst O X T d hloc E₁.1 (congrArg Subtype.val hE1.eq)
      (charT O X T d G r hG1 E₁.1 E₁.2) x π, hrB]
  · rw [rankConst O X T d hloc E₂.1 (congrArg Subtype.val hE2.eq)
      (charT O X T d G r hG1 E₂.1 E₂.2) x π, hr1]

end Formalism.RepresentationBoundsCohomology.ringDataObjects
