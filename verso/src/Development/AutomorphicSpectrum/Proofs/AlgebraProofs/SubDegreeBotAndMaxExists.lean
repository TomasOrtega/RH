import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BundleDegreeEqSumValuationsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeMonoLatticeLeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundlesStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubDegreeNonposTrivialLatticeStatement

noncomputable section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax

variable {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]

def latOf (i : C.I) {n : ℕ} (b : Module.Basis (Fin n) K V) : AddSubgroup V where
  carrier := {x | ∀ q, C.v i (b.repr x q) ≤ 1}
  zero_mem' := fun q => by simp
  add_mem' := fun {x y} hx hy q => by
    rw [map_add, Finsupp.add_apply]; exact (C.v i).map_add_le (hx q) (hy q)
  neg_mem' := fun {x} hx q => by
    rw [map_neg, Finsupp.neg_apply, Valuation.map_neg]; exact hx q

/- English proof (translation)
Introduce `_` and use `Iff.rfl`.
-/
theorem isLatOf_latOf (i : C.I) {n : ℕ} (b : Module.Basis (Fin n) K V) :
    IsLatOf C i b (latOf C i b) := fun _ => Iff.rfl

def scale (L : C.I → AddSubgroup V) (c : C.I → Kˣ) : C.I → AddSubgroup V :=
  fun i => (L i).comap (DistribSMul.toAddMonoidHom V (((c i)⁻¹ : Kˣ) : K))

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_scale (L : C.I → AddSubgroup V) (c : C.I → Kˣ) (i : C.I) (x : V) :
    x ∈ scale C L c i ↔ (((c i)⁻¹ : Kˣ) : K) • x ∈ L i := Iff.rfl

/- English proof (translation)
Introduce `x`. Rewrite using `[mem_scale, h]`. Use `forall_congr' fun q => ?_` and prove the remaining obligations. Rewrite using `[Module.Basis.repr_unitsSMul, map_smul, Finsupp.smul_apply]`. Both sides reduce to the same expression.
-/
theorem isLatOf_scale {L : C.I → AddSubgroup V} (c : C.I → Kˣ) {i : C.I} {n : ℕ}
    {b : Module.Basis (Fin n) K V} (h : IsLatOf C i b (L i)) :
    IsLatOf C i (b.unitsSMul fun _ => c i) (scale C L c i) := by
  intro x
  rw [mem_scale, h]
  refine forall_congr' fun q => ?_
  rw [Module.Basis.repr_unitsSMul, map_smul, Finsupp.smul_apply]
  rfl

/- English proof (translation)
Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `h.1 i`. Conclude with `⟨_, isLatOf_scale C c hb⟩`. Take `⟨b, hb⟩` from `h.2`. Use `⟨b, (hb.union hc).subset fun i hi => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hn`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn hi`. Apply `hi` to reduce the goal to its premises. Introduce `x`. Rewrite using `[mem_scale, hn.2, inv_one, Units.val_one, one_smul]`.

Conclude with `hn.1 x`.
-/
theorem isBun_scale {L : C.I → AddSubgroup V} (c : C.I → Kˣ) (hc : {i | c i ≠ 1}.Finite)
    (h : IsBun C L) : IsBun C (scale C L c) := by
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := h.1 i
    exact ⟨_, isLatOf_scale C c hb⟩
  · obtain ⟨b, hb⟩ := h.2
    refine ⟨b, (hb.union hc).subset fun i hi => ?_⟩
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn hi
    apply hi
    intro x
    rw [mem_scale, hn.2, inv_one, Units.val_one, one_smul]
    exact hn.1 x

/- English proof (translation)
Use `choose b hb using h.1`. Take `⟨hf, e⟩` from `GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L _ (Module.finBasis K V) b h hb`. Take `⟨-, e'⟩` from `GlobalTheory.T.bundle_degree_eq_sum_valuations K C V (scale C L c) _ (Module.finBasis K V) (fun i => (b i).unitsSMul fun _ => c i) (isBun_scale C c hc h) (fun i => isLatOf_scale C c (hb i))`. Establish `hs1 : (Function.support fun i => (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i)))).Finite`. Use `hf.subset fun i hi => ?_` and prove the remaining obligations.

Introduce `h1`. Conclude with `hi (by simp [h1])`. Establish `hs3 : (Function.support fun i => (Module.finrank K V : ℤ) * ((C.w i : ℤ) * WithZero.log (C.v i (c i)))).Finite`. Use `hc.subset fun i hi => ?_` and prove the remaining obligations. Introduce `h1`.

Conclude with `hi (by simp [h1])`. Rewrite using `[e, e', mul_finsum, ← finsum_add_distrib hs1 hs3]`. Use `finsum_congr fun i => ?_` and prove the remaining obligations. Establish `hd : (Module.finBasis K V).det ((b i).unitsSMul fun _ => c i) = (c i : K) ^ Module.finrank K V * (Module.finBasis K V).det (b i)`. Establish `: ⇑((b i).unitsSMul fun _ => c i) = fun j => (c i : K) • b i j`.

Use function extensionality and compare the values at `j`. Rewrite using `[Module.Basis.unitsSMul_apply]`. Both sides reduce to the same expression. Rewrite using `[this]`. Use `(Module.finBasis K V).det.toMultilinearMap.map_smul_univ (fun _ => (c i : K)) (b i)` as an intermediate fact.

Simplify using `using this`. Establish `h0 : C.v i ((Module.finBasis K V).det (b i)) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`. Conclude with `((Module.finBasis K V).isUnit_det (b i)).ne_zero`. Establish `h1 : C.v i (c i) ≠ 0`.

Rewrite using `[Valuation.ne_zero_iff]`. Conclude with `(c i).ne_zero`. Rewrite using `[hd, map_mul, map_pow, WithZero.log_mul (pow_ne_zero _ h1) h0, WithZero.log_pow]`. Simplify using `only [nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deg_scale [FiniteDimensional K V] {L : C.I → AddSubgroup V} (c : C.I → Kˣ)
    (hc : {i | c i ≠ 1}.Finite) (h : IsBun C L) :
    deg C (scale C L c) = deg C L +
      (Module.finrank K V : ℤ) * ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (c i)) := by
  choose b hb using h.1
  obtain ⟨hf, e⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V L _ (Module.finBasis K V) b h hb
  obtain ⟨-, e'⟩ := GlobalTheory.T.bundle_degree_eq_sum_valuations K C V (scale C L c) _ (Module.finBasis K V)
    (fun i => (b i).unitsSMul fun _ => c i) (isBun_scale C c hc h)
    (fun i => isLatOf_scale C c (hb i))
  have hs1 : (Function.support fun i =>
      (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i)))).Finite := by
    refine hf.subset fun i hi => ?_
    intro h1
    exact hi (by simp [h1])
  have hs3 : (Function.support fun i => (Module.finrank K V : ℤ) *
      ((C.w i : ℤ) * WithZero.log (C.v i (c i)))).Finite := by
    refine hc.subset fun i hi => ?_
    intro h1
    exact hi (by simp [h1])
  rw [e, e', mul_finsum, ← finsum_add_distrib hs1 hs3]
  refine finsum_congr fun i => ?_
  have hd : (Module.finBasis K V).det ((b i).unitsSMul fun _ => c i) =
      (c i : K) ^ Module.finrank K V * (Module.finBasis K V).det (b i) := by
    have : ⇑((b i).unitsSMul fun _ => c i) = fun j => (c i : K) • b i j := by
      funext j; rw [Module.Basis.unitsSMul_apply]; rfl
    rw [this]
    have := (Module.finBasis K V).det.toMultilinearMap.map_smul_univ (fun _ => (c i : K)) (b i)
    simpa using this
  have h0 : C.v i ((Module.finBasis K V).det (b i)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact ((Module.finBasis K V).isUnit_det (b i)).ne_zero
  have h1 : C.v i (c i) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact (c i).ne_zero
  rw [hd, map_mul, map_pow, WithZero.log_mul (pow_ne_zero _ h1) h0, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

/- English proof (translation)
Take `⟨c, -, hc⟩` from `Finset.exists_max_image (insert (1 : K) (Finset.univ.image fun p : Fin m × Fin n => b.repr (b' p.1) p.2)) (C.v i) (Finset.insert_nonempty _ _)`. Establish `h1 : 1 ≤ C.v i c` using `by simpa using hc 1 (Finset.mem_insert_self _ _)`. Establish `hpos : 0 < C.v i c` using `lt_of_lt_of_le zero_lt_one h1`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at hpos`. Use `⟨Units.mk0 c hc0, h1, fun x hx q => ?_⟩` and prove the remaining obligations. Establish `hle : C.v i (b.repr x q) ≤ C.v i c`. Establish `hx' : b.repr x q = ∑ j, b'.repr x j * b.repr (b' j) q` using `by conv_lhs => rw [← b'.sum_repr x]`. Rewrite using `[map_sum, Finsupp.finset_sum_apply]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`. Rewrite using `[hx']`. Use `(C.v i).map_sum_le fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, inv_mul_le_iff₀ hpos, mul_one]`. Conclude with `hle`.
-/
theorem exists_scale (i : C.I) {n m : ℕ} (b : Module.Basis (Fin n) K V)
    {b' : Module.Basis (Fin m) K V} {L : AddSubgroup V} (h : IsLatOf C i b' L) :
    ∃ c : Kˣ, 1 ≤ C.v i c ∧ ∀ x ∈ L, ((c⁻¹ : Kˣ) : K) • x ∈ latOf C i b := by
  classical
  obtain ⟨c, -, hc⟩ := Finset.exists_max_image
    (insert (1 : K) (Finset.univ.image fun p : Fin m × Fin n => b.repr (b' p.1) p.2))
    (C.v i) (Finset.insert_nonempty _ _)
  have h1 : 1 ≤ C.v i c := by simpa using hc 1 (Finset.mem_insert_self _ _)
  have hpos : 0 < C.v i c := lt_of_lt_of_le zero_lt_one h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hpos
  refine ⟨Units.mk0 c hc0, h1, fun x hx q => ?_⟩
  have hle : C.v i (b.repr x q) ≤ C.v i c := by
    have hx' : b.repr x q = ∑ j, b'.repr x j * b.repr (b' j) q := by
      conv_lhs => rw [← b'.sum_repr x]
      rw [map_sum, Finsupp.finset_sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [hx']
    refine (C.v i).map_sum_le fun j _ => ?_
    rw [map_mul]
    calc _ ≤ 1 * C.v i c := mul_le_mul' ((h x).1 hx j)
          (hc _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(j, q), Finset.mem_univ _, rfl⟩)))
      _ = _ := one_mul _
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, Units.val_mk0,
    map_inv₀, inv_mul_le_iff₀ hpos, mul_one]
  exact hle

/- English proof (translation)
Unfold `subDeg deg`. Establish `: IsEmpty (Fin (Module.finrank K (⊥ : Submodule K V)))`. Rewrite using `[finrank_bot]`. Use `infer_instance`. Use `finsum_eq_zero_of_forall_eq_zero fun i => ?_` and prove the remaining obligations.

Simplify using `[Module.Basis.det_apply]`.
-/
theorem subDeg_bot [FiniteDimensional K V] (L : C.I → AddSubgroup V) : subDeg C L ⊥ = 0 := by
  unfold subDeg deg
  have : IsEmpty (Fin (Module.finrank K (⊥ : Submodule K V))) := by
    rw [finrank_bot]; infer_instance
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  simp [Module.Basis.det_apply]

/- English proof (translation)
Take `⟨b, hb⟩` from `h.2`. Establish `key : ∀ i, ∃ c : Kˣ, (IsLatOf C i b (L i) → c = 1) ∧ 1 ≤ C.v i c ∧ ∀ x ∈ L i, ((c⁻¹ : Kˣ) : K) • x ∈ latOf C i b`. Introduce `i`. Distinguish the cases in `hi : IsLatOf C i b (L i)`. Use `⟨1, fun _ => rfl, by simp, fun x hx => ?_⟩` and prove the remaining obligations.

Rewrite using `[inv_one, Units.val_one, one_smul]`. Conclude with `(hi x).1 hx`. Take `⟨b', hb'⟩` from `h.1 i`. Take `⟨c, h1, h2⟩` from `exists_scale C i b hb'`. Conclude with `⟨c, fun h' => absurd h' hi, h1, h2⟩`.

Use `choose c hc1 hc2 hc3 using key`. Establish `hc : {i | c i ≠ 1}.Finite` using `hb.subset fun i hi h' => hi (hc1 i h')`. Establish `h0 : IsBun C (fun i => latOf C i b)` using `⟨fun i => ⟨b, isLatOf_latOf C i b⟩, b, by simp [isLatOf_latOf]⟩`. Use `set S : ℤ := ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (c i)) with hS`. Establish `hS0 : 0 ≤ S`.

Use `finsum_nonneg fun i => mul_nonneg (Int.natCast_nonneg _) ?_` and prove the remaining obligations. Establish `h1 : C.v i (c i) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`. Conclude with `(c i).ne_zero`. Use `(WithZero.log_le_log one_ne_zero h1).2 (hc2 i)` as an intermediate fact.

Simplify using `using this`. Use `⟨(Module.finrank K V : ℤ) * S, fun W => ?_⟩` and prove the remaining obligations. Establish `hW` using `(GlobalTheory.T.sub_and_quotient_bundles K C V _ W h0).1`. Establish `e1` using `GlobalTheory.T.degree_mono_lattice_le K C W (sub C L W) (scale C (sub C (fun i => latOf C i b) W) c) (GlobalTheory.T.sub_and_quotient_bundles K C V _ W h).1 (isBun_scale C c hc hW) (fun i x hx => hc3 i x hx)`. Establish `e2` using `deg_scale C c hc hW`.

Establish `e3` using `GlobalTheory.T.sub_degree_nonpos_trivial_lattice K C V _ b (fun i => latOf C i b) W (fun i => isLatOf_latOf C i b)`. Establish `e4 : (Module.finrank K W : ℤ) * S ≤ (Module.finrank K V : ℤ) * S` using `mul_le_mul_of_nonneg_right (by exact_mod_cast W.finrank_le) hS0`. Unfold `subDeg at e3 ⊢`. Rewrite `e2` using `[← hS]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem subDeg_bdd [FiniteDimensional K V] (L : C.I → AddSubgroup V) (h : IsBun C L) :
    ∃ B : ℤ, ∀ W : Submodule K V, subDeg C L W ≤ B := by
  classical
  obtain ⟨b, hb⟩ := h.2
  have key : ∀ i, ∃ c : Kˣ, (IsLatOf C i b (L i) → c = 1) ∧ 1 ≤ C.v i c ∧
      ∀ x ∈ L i, ((c⁻¹ : Kˣ) : K) • x ∈ latOf C i b := by
    intro i
    by_cases hi : IsLatOf C i b (L i)
    · refine ⟨1, fun _ => rfl, by simp, fun x hx => ?_⟩
      rw [inv_one, Units.val_one, one_smul]
      exact (hi x).1 hx
    · obtain ⟨b', hb'⟩ := h.1 i
      obtain ⟨c, h1, h2⟩ := exists_scale C i b hb'
      exact ⟨c, fun h' => absurd h' hi, h1, h2⟩
  choose c hc1 hc2 hc3 using key
  have hc : {i | c i ≠ 1}.Finite := hb.subset fun i hi h' => hi (hc1 i h')
  have h0 : IsBun C (fun i => latOf C i b) :=
    ⟨fun i => ⟨b, isLatOf_latOf C i b⟩, b, by simp [isLatOf_latOf]⟩
  set S : ℤ := ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (c i)) with hS
  have hS0 : 0 ≤ S := by
    refine finsum_nonneg fun i => mul_nonneg (Int.natCast_nonneg _) ?_
    have h1 : C.v i (c i) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact (c i).ne_zero
    have := (WithZero.log_le_log one_ne_zero h1).2 (hc2 i)
    simpa using this
  refine ⟨(Module.finrank K V : ℤ) * S, fun W => ?_⟩
  have hW := (GlobalTheory.T.sub_and_quotient_bundles K C V _ W h0).1
  have e1 := GlobalTheory.T.degree_mono_lattice_le K C W (sub C L W) (scale C (sub C (fun i => latOf C i b) W) c)
    (GlobalTheory.T.sub_and_quotient_bundles K C V _ W h).1 (isBun_scale C c hc hW) (fun i x hx => hc3 i x hx)
  have e2 := deg_scale C c hc hW
  have e3 := GlobalTheory.T.sub_degree_nonpos_trivial_lattice K C V _ b (fun i => latOf C i b) W (fun i => isLatOf_latOf C i b)
  have e4 : (Module.finrank K W : ℤ) * S ≤ (Module.finrank K V : ℤ) * S :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast W.finrank_le) hS0
  unfold subDeg at e3 ⊢
  rw [← hS] at e2
  linarith

/- English proof (translation)
Introduce `K _ C V _ _ _ L h`. Use `⟨subDeg_bot C L, ?_⟩` and prove the remaining obligations. Take `⟨B, hB⟩` from `subDeg_bdd C L h`. Take `⟨z, ⟨W₀, rfl⟩, hz⟩` from `Int.exists_greatest_of_bdd (P := fun z => ∃ W : Submodule K V, subDeg C L W = z) ⟨B, by rintro _ ⟨W, rfl⟩; exact hB W⟩ ⟨_, ⊥, rfl⟩`. Conclude with `⟨W₀, fun W => hz _ ⟨W, rfl⟩⟩`.
-/
theorem subDeg_max : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (L : C.I → AddSubgroup V), IsBun C L →
    subDeg C L ⊥ = 0 ∧ ∃ W₀ : Submodule K V, ∀ W : Submodule K V, subDeg C L W ≤ subDeg C L W₀ := by
  intro K _ C V _ _ _ L h
  refine ⟨subDeg_bot C L, ?_⟩
  obtain ⟨B, hB⟩ := subDeg_bdd C L h
  obtain ⟨z, ⟨W₀, rfl⟩, hz⟩ := Int.exists_greatest_of_bdd
    (P := fun z => ∃ W : Submodule K V, subDeg C L W = z)
    ⟨B, by rintro _ ⟨W, rfl⟩; exact hB W⟩ ⟨_, ⊥, rfl⟩
  exact ⟨W₀, fun W => hz _ ⟨W, rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax
