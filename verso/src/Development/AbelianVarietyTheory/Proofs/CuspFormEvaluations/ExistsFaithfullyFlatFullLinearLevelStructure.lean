import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsIdempotentElemRangeSpMapSubset
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FaithfullyFlatPointsBaseChangeDescent
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFlatUniversalTorsionTuple

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LevelFlat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Establish `: Module.Finite (𝓞 E) Dw.La` using `Dw.fin`. Establish `: Module.Finite ℤ Dw.La` using `Module.Finite.trans (𝓞 E) Dw.La`. Use `set N : Submodule ℤ Dw.La := LinearMap.range ((k : ℤ) • LinearMap.id : Dw.La →ₗ[ℤ] Dw.La) with hN`. Establish `hmem : ∀ x : Dw.La, x ∈ N ↔ Dw.ModN k x`. Introduce `x`.

Rewrite using `[hN, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Conclude with `⟨y, by rw [← hy]; simp⟩`. Introduce and unpack `⟨y, hy⟩`.

Conclude with `⟨y, by rw [hy]; simp⟩`. Establish `htor : Module.IsTorsion ℤ (Dw.La ⧸ N)`. Introduce `x`. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H a`.

Use `⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩` and prove the remaining obligations. Use `show ((k : ℤ)) • (Submodule.Quotient.mk a : Dw.La ⧸ N) = 0`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hmem]`. Conclude with `⟨a, by simp⟩`. Establish `: Finite (Dw.La ⧸ N)` using `Module.finite_of_fg_torsion _ htor`.

Use `⟨Dw.La ⧸ N, Fintype.ofFinite _, N.mkQ, Function.surjInv N.mkQ_surjective, fun j => Function.surjInv_eq N.mkQ_surjective j, ?_⟩` and prove the remaining obligations. Introduce `a b`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hmem]`.
-/
theorem exists_finite_quotient (Dw : Datum H) (k : ℕ) (hk : 0 < k) :
    ∃ (J : Type) (_ : Fintype J) (π : Dw.La → J) (r : J → Dw.La), (∀ j, π (r j) = j) ∧
      ∀ a b, π a = π b ↔ Dw.ModN k (a - b) := by
  have : Module.Finite (𝓞 E) Dw.La := Dw.fin
  have : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
  set N : Submodule ℤ Dw.La := LinearMap.range ((k : ℤ) • LinearMap.id : Dw.La →ₗ[ℤ] Dw.La) with hN
  have hmem : ∀ x : Dw.La, x ∈ N ↔ Dw.ModN k x := by
    intro x
    rw [hN, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [← hy]; simp⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [hy]; simp⟩
  have htor : Module.IsTorsion ℤ (Dw.La ⧸ N) := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H a =>
      refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
      show ((k : ℤ)) • (Submodule.Quotient.mk a : Dw.La ⧸ N) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hmem]
      exact ⟨a, by simp⟩
  have : Finite (Dw.La ⧸ N) := Module.finite_of_fg_torsion _ htor
  refine ⟨Dw.La ⧸ N, Fintype.ofFinite _, N.mkQ, Function.surjInv N.mkQ_surjective,
    fun j => Function.surjInv_eq N.mkQ_surjective j, ?_⟩
  intro a b
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hmem]

/- English proof (translation)
The claim follows from `hu.mul_left_cancel (by rw [_root_.mul_one]; exact h)`.
-/
private lemma eq_one_of_isIdempotentElem_of_isUnit {T : Type} [CommRing T] {x : T} (h : IsIdempotentElem x) (hu : IsUnit x) :
    x = 1 :=
  hu.mul_left_cancel (by rw [_root_.mul_one]; exact h)

/- English proof (translation)
Establish `hA : ∀ i, ∃ e : B, IsIdempotentElem e ∧ ∀ (T : Type) [CommRing T] (χ : B →+* T), χ e = 1 ↔ spMap χ ≫ (a i).left = spMap χ ≫ (b i).left` using `fun i => exists_isIdempotentElem_torsion_eq hL E H Dw l Xo B x0 k hk (a i) (b i) (ha i) (hb i)`. Establish `hC : ∀ j, ∃ e : B, IsIdempotentElem e ∧ ∀ (T : Type) [CommRing T] (χ : B →+* T), χ e = 1 ↔ spMap χ ≫ (c j).left = spMap χ ≫ (d j).left` using `fun j => exists_isIdempotentElem_torsion_eq hL E H Dw l Xo B x0 k hk (c j) (d j) (hc j) (hd j)`. Use `choose ea hea hea' using hA`. Use `choose ec hec hec' using hC`. Use `⟨(∏ i, ea i) * ∏ j, (1 - ec j), ?_, ?_⟩` and prove the remaining obligations.

Introduce `T _ χ hu`. Rewrite `hu` using `[map_mul, map_prod, map_prod]`. Use `⟨fun i => ?_, fun hT j hj => ?_⟩` and prove the remaining obligations. Establish `hui : IsUnit (χ (ea i))` using `isUnit_of_dvd_unit (dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _) hu`. Conclude with `(hea' i T χ).mp (eq_one_of_isIdempotentElem_of_isUnit ((hea i).map χ) hui)`.

Establish `huj : IsUnit (χ (1 - ec j))` using `isUnit_of_dvd_unit (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _) hu`. Establish `h1 : χ (1 - ec j) = 1` using `eq_one_of_isIdempotentElem_of_isUnit (((hec j).one_sub).map χ) huj`. Establish `h2 : χ (ec j) = 1` using `(hec' j T χ).mpr hj`. Rewrite `h1` using `[map_sub, map_one, h2, sub_self]`. Conclude with `zero_ne_one h1`.

Introduce `K _ χ heq hne`. Establish `h1 : ∀ i, χ (ea i) = 1` using `fun i => (hea' i K χ).mpr (heq i)`. Establish `h0 : ∀ j, χ (ec j) = 0`. Introduce `j`. Break down `IsIdempotentElem.iff_eq_zero_or_one.mp ((hec j).map χ) with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd ((hec' j K χ).mp h) (hne j)`. Rewrite using `[map_mul, map_prod, map_prod]`. Simplify using `[h1, h0]`.
-/
theorem exists_element (hL : Laws) {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (B : Type) [CommRing B]
    (x0 : Sp B ⟶ Xo.X) (k : ℕ) (hk : 0 < k) (I I' : Type) [Fintype I] [Fintype I']
    (a b : I → (ptO Xo x0 ⟶ Xo.univ.t.G)) (c d : I' → (ptO Xo x0 ⟶ Xo.univ.t.G))
    (ha : ∀ i, a i ^ k = 1) (hb : ∀ i, b i ^ k = 1) (hc : ∀ i, c i ^ k = 1) (hd : ∀ i, d i ^ k = 1) :
    ∃ e : B, (∀ (T : Type) [CommRing T] (χ : B →+* T), IsUnit (χ e) →
        (∀ i, spMap χ ≫ (a i).left = spMap χ ≫ (b i).left) ∧
          (Nontrivial T → ∀ j, spMap χ ≫ (c j).left ≠ spMap χ ≫ (d j).left)) ∧
      ∀ (K : Type) [Field K] (χ : B →+* K), (∀ i, spMap χ ≫ (a i).left = spMap χ ≫ (b i).left) →
        (∀ j, spMap χ ≫ (c j).left ≠ spMap χ ≫ (d j).left) → IsUnit (χ e) := by
  have hA : ∀ i, ∃ e : B, IsIdempotentElem e ∧ ∀ (T : Type) [CommRing T] (χ : B →+* T),
      χ e = 1 ↔ spMap χ ≫ (a i).left = spMap χ ≫ (b i).left := fun i =>
    exists_isIdempotentElem_torsion_eq hL E H Dw l Xo B x0 k hk (a i) (b i) (ha i) (hb i)
  have hC : ∀ j, ∃ e : B, IsIdempotentElem e ∧ ∀ (T : Type) [CommRing T] (χ : B →+* T),
      χ e = 1 ↔ spMap χ ≫ (c j).left = spMap χ ≫ (d j).left := fun j =>
    exists_isIdempotentElem_torsion_eq hL E H Dw l Xo B x0 k hk (c j) (d j) (hc j) (hd j)
  choose ea hea hea' using hA
  choose ec hec hec' using hC
  refine ⟨(∏ i, ea i) * ∏ j, (1 - ec j), ?_, ?_⟩
  · intro T _ χ hu
    rw [map_mul, map_prod, map_prod] at hu
    refine ⟨fun i => ?_, fun hT j hj => ?_⟩
    · have hui : IsUnit (χ (ea i)) :=
        isUnit_of_dvd_unit (dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _) hu
      exact (hea' i T χ).mp (eq_one_of_isIdempotentElem_of_isUnit ((hea i).map χ) hui)
    · have huj : IsUnit (χ (1 - ec j)) :=
        isUnit_of_dvd_unit (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _) hu
      have h1 : χ (1 - ec j) = 1 := eq_one_of_isIdempotentElem_of_isUnit (((hec j).one_sub).map χ) huj
      have h2 : χ (ec j) = 1 := (hec' j T χ).mpr hj
      rw [map_sub, map_one, h2, sub_self] at h1
      exact zero_ne_one h1
  · intro K _ χ heq hne
    have h1 : ∀ i, χ (ea i) = 1 := fun i => (hea' i K χ).mpr (heq i)
    have h0 : ∀ j, χ (ec j) = 0 := by
      intro j
      rcases IsIdempotentElem.iff_eq_zero_or_one.mp ((hec j).map χ) with h | h
      · exact h
      · exact absurd ((hec' j K χ).mp h) (hne j)
    rw [map_mul, map_prod, map_prod]
    simp [h1, h0]

/- English proof (translation)
Establish `hev0 : ev 0 = 1`. Establish `h0` using `hadd 0 0`. Rewrite `h0` using `[add_zero]`. Conclude with `mul_left_cancel (a := ev 0) (by rw [_root_.mul_one]; exact h0.symm)`. Establish `hact0 : A.act 0 = 1`.

Establish `h0` using `A.add 0 0`. Rewrite `h0` using `[add_zero]`. Conclude with `mul_left_cancel (a := A.act 0) (by rw [_root_.mul_one]; exact h0.symm)`. Establish `hevneg : ∀ b, ev (-b) = (ev b)⁻¹`. Introduce `b`.

Establish `h0` using `hadd b (-b)`. Rewrite `h0` using `[add_neg_cancel, hev0]`. Conclude with `eq_inv_of_mul_eq_one_right h0.symm`. Establish `hactneg : ∀ o, A.act (-o) = (A.act o)⁻¹`. Introduce `o`.

Establish `h0` using `A.add o (-o)`. Rewrite `h0` using `[add_neg_cancel, hact0]`. Conclude with `eq_inv_of_mul_eq_one_right h0.symm`. Establish `key : ∀ x ∈ AddSubgroup.closure s, ∀ a, ev (x • a) = ev a ≫ A.act x`. Introduce `x hx`.

Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem y hy => exact h y hy`. Consider the case `zero => intro a`. Rewrite using `[zero_smul, hev0, hact0, MonObj.comp_one]`. Consider the case `add y z _ _ hy hz => intro a`.

Rewrite using `[add_smul, hadd, hy, hz, A.add, MonObj.comp_mul]`. Consider the case `neg y _ hy => intro a`. Rewrite using `[neg_smul, hevneg, hy, hactneg, GrpObj.comp_inv]`. Conclude with `key o (by rw [hs]; exact AddSubgroup.mem_top o) a`.
-/
theorem lin_of_generators {X : Scheme.{0}} {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {G T : Over X}
    [GrpObj G] (A : Geo.Tor.OAct O G) (ev : M → (T ⟶ G)) (hadd : ∀ a b, ev (a + b) = ev a * ev b) {s : Set O}
    (hs : AddSubgroup.closure s = ⊤) (h : ∀ o ∈ s, ∀ a, ev (o • a) = ev a ≫ A.act o) (o : O) (a : M) :
    ev (o • a) = ev a ≫ A.act o := by
  have hev0 : ev 0 = 1 := by
    have h0 := hadd 0 0
    rw [add_zero] at h0
    exact mul_left_cancel (a := ev 0) (by rw [_root_.mul_one]; exact h0.symm)
  have hact0 : A.act 0 = 1 := by
    have h0 := A.add 0 0
    rw [add_zero] at h0
    exact mul_left_cancel (a := A.act 0) (by rw [_root_.mul_one]; exact h0.symm)
  have hevneg : ∀ b, ev (-b) = (ev b)⁻¹ := by
    intro b
    have h0 := hadd b (-b)
    rw [add_neg_cancel, hev0] at h0
    exact eq_inv_of_mul_eq_one_right h0.symm
  have hactneg : ∀ o, A.act (-o) = (A.act o)⁻¹ := by
    intro o
    have h0 := A.add o (-o)
    rw [add_neg_cancel, hact0] at h0
    exact eq_inv_of_mul_eq_one_right h0.symm
  have key : ∀ x ∈ AddSubgroup.closure s, ∀ a, ev (x • a) = ev a ≫ A.act x := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy => exact h y hy
    | zero => intro a; rw [zero_smul, hev0, hact0, MonObj.comp_one]
    | add y z _ _ hy hz => intro a; rw [add_smul, hadd, hy, hz, A.add, MonObj.comp_mul]
    | neg y _ hy => intro a; rw [neg_smul, hevneg, hy, hactneg, GrpObj.comp_inv]
  exact key o (by rw [hs]; exact AddSubgroup.mem_top o) a

/- English proof (translation)
Simplify using `[spMap, CommRingCat.ofHom_comp]`.
-/
private lemma spMap_comp_moduli_spaces {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
    (f : R →+* R') (g : R' →+* R'') : spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp]

/- English proof (translation)
Take `⟨u, rfl⟩` from `hx`. Take `⟨v, rfl⟩` from `hy`. Conclude with `⟨u + v, (smul_add k u v).symm⟩`.
-/
private lemma modN_add' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {k : ℕ} {x y : Dw.La} (hx : Dw.ModN k x) (hy : Dw.ModN k y) :
    Dw.ModN k (x + y) := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  exact ⟨u + v, (smul_add k u v).symm⟩

/- English proof (translation)
Take `⟨u, rfl⟩` from `hx`. Conclude with `⟨-u, (smul_neg k u).symm⟩`.
-/
private lemma modN_neg' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {k : ℕ} {x : Dw.La} (hx : Dw.ModN k x) : Dw.ModN k (-x) := by
  obtain ⟨u, rfl⟩ := hx
  exact ⟨-u, (smul_neg k u).symm⟩

/- English proof (translation)
Take `⟨u, rfl⟩` from `hx`. Conclude with `⟨o • u, smul_comm o k u⟩`.
-/
private lemma modN_smul' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {k : ℕ} (o : 𝓞 E) {x : Dw.La} (hx : Dw.ModN k x) : Dw.ModN k (o • x) := by
  obtain ⟨u, rfl⟩ := hx
  exact ⟨o • u, smul_comm o k u⟩

end LevelFlat

open LevelFlat in

/- English proof (translation)
Introduce `hL E _ _ _ H Dw l Xo S _ x0 k hk`. Take `⟨J, hJ, π, r, hπr, hπ⟩` from `exists_finite_quotient Dw k hk`. Take `⟨B, _, φ, w, hφ, hw, huniv⟩` from `exists_flat_universal_torsion_tuple hL E H Dw l Xo S x0 k hk J`. Take `⟨t, ht⟩` from `(Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)`. Establish `hgen : AddSubgroup.closure (t : Set (𝓞 E)) = ⊤`.

Rewrite using `[← Submodule.span_int_eq_addSubgroupClosure, ht]`. Simplify using the standard rewrite rules. Establish `hrep : ∀ a, Dw.ModN k (a - r (π a))` using `fun a => (hπ a (r (π a))).mp (hπr (π a)).symm`. Set `fa : (J × J) ⊕ (t × J) → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)` to `Sum.elim (fun p => w (π (r p.1 + r p.2))) (fun q => w (π ((q.1 : 𝓞 E) • r q.2)))`. Set `fb : (J × J) ⊕ (t × J) → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)` to `Sum.elim (fun p => w p.1 * w p.2) (fun q => w q.2 ≫ Xo.univ.t.act.act (q.1 : 𝓞 E))`.

Set `fc : {p : J × J // p.1 ≠ p.2} → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)` to `fun p => w p.1.1`. Set `fd : {p : J × J // p.1 ≠ p.2} → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)` to `fun p => w p.1.2`. Establish `hfa : ∀ i, fa i ^ k = 1`. Apply the tactic sequence `rintro (p | q) <;> exact hw _`. Establish `hfb : ∀ i, fb i ^ k = 1`.

Introduce and unpack `(p | q)`. Use `show (w p.1 * w p.2) ^ k = 1`. Rewrite using `[mul_pow, hw, hw, _root_.mul_one]`. Use `show (w q.2 ≫ Xo.univ.t.act.act (q.1 : 𝓞 E)) ^ k = 1`. Use `Xo.univ.t.act.hom (q.1 : 𝓞 E)` as an intermediate fact.

Rewrite using `[← MonObj.pow_comp, hw, MonObj.one_comp]`. Take `⟨e, he1, he2⟩` from `exists_element hL Xo B (spMap φ ≫ x0) k hk _ _ fa fb fc fd hfa hfb (fun p => hw _) (fun p => hw _)`. Use `set B' := Localization.Away e`. Use `set alg := algebraMap B B'`. Establish `halg : spMap alg ≫ (spMap φ ≫ x0) = spMap (alg.comp φ) ≫ x0`.

Rewrite using `[spMap_comp_moduli_spaces φ alg, Category.assoc]`. Set `m : ptO Xo (spMap (alg.comp φ) ≫ x0) ⟶ ptO Xo (spMap φ ≫ x0)` to `Over.homMk (spMap alg) halg`. Establish `hm : ∀ f : ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G, (m ≫ f).left = spMap alg ≫ f.left`. Introduce `f`. Both sides reduce to the same expression.

Establish `hunit : IsUnit (alg e)` using `IsLocalization.Away.algebraMap_isUnit e`. Take `⟨heq, hne⟩` from `he1 B' alg hunit`. Establish `heq' : ∀ i, m ≫ fa i = m ≫ fb i` using `fun i => Over.OverMorphism.ext (by rw [hm, hm]; exact heq i)`. Set `ev : Dw.La → (ptO Xo (spMap (alg.comp φ) ≫ x0) ⟶ Xo.univ.t.G)` to `fun a => m ≫ w (π a)`. Establish `hadd : ∀ a b, ev (a + b) = ev a * ev b`.

Introduce `a b`. Establish `hab : π (a + b) = π (r (π a) + r (π b))`. Rewrite using `[hπ]`. Use `modN_add' (hrep a) (hrep b)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Normalize the expressions using the abelian group laws. Use `show m ≫ w (π (a + b)) = (m ≫ w (π a)) * (m ≫ w (π b))`. Rewrite using `[hab, ← MonObj.comp_mul]`. Conclude with `heq' (Sum.inl (π a, π b))`. Establish `hev0 : ev 0 = 1`.

Establish `h0` using `hadd 0 0`. Rewrite `h0` using `[add_zero]`. Conclude with `mul_left_cancel (a := ev 0) (by rw [_root_.mul_one]; exact h0.symm)`. Establish `hpow : ∀ (n : ℕ) a, ev (n • a) = ev a ^ n`. Introduce `n a`.

Proceed by induction on `n with`. Consider the case `zero => rw [zero_smul, pow_zero, hev0]`. Consider the case `succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]`. Use `⟨B', inferInstance, alg.comp φ, ev, ?_, hadd, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]`.

Use `⟨RingHom.Flat.comp hφ ?_, ?_⟩` and prove the remaining obligations. Conclude with `RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B' (Submonoid.powers e))`. Introduce `p set κ := p.asIdeal.ResidueField set Kp := AlgebraicClosure κ set ψ : S →+* Kp := (algebraMap κ Kp).comp (algebraMap S κ) with hψ set xp : Sp Kp ⟶ Xo.X := spMap ψ ≫ x0`. Establish `hβ : xp ≫ Xo.s = spMap (Spec.preimage (xp ≫ Xo.s)).hom`. Simplify using `[spMap]`.

Take `⟨_, I, _, _, _⟩` from `Xo.univ.geom Kp xp _ hβ`. Set `u : J → (ptO Xo (spMap ψ ≫ x0) ⟶ Xo.univ.t.G)` to `fun j => I.ev k (r j)`. Establish `hu : ∀ j, u j ^ k = 1` using `fun j => (I.onto k hk (u j)).mpr ⟨r j, rfl⟩`. Take `⟨χ, hχφ, hχu⟩` from `huniv Kp ψ u hu`. Establish `hmχ : spMap χ ≫ (spMap φ ≫ x0) = spMap ψ ≫ x0`.

Rewrite using `[← hχφ, spMap_comp_moduli_spaces φ χ, Category.assoc]`. Set `mχ : ptO Xo (spMap ψ ≫ x0) ⟶ ptO Xo (spMap φ ≫ x0)` to `Over.homMk (spMap χ) hmχ`. Establish `hmχw : ∀ j, mχ ≫ w j = u j` using `fun j => Over.OverMorphism.ext (by rw [hχu j]; rfl)`. Establish `hIeq : ∀ a b, I.ev k a = I.ev k b ↔ Dw.ModN k (a - b)`. Introduce `a b`.

Establish `hsplit` using `I.add k (a - b) b`. Rewrite `hsplit` using `[sub_add_cancel]`. Use `show _ ↔ ∃ c, a - b = k • c`. Rewrite using `[← I.ker k hk (a - b)]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite `hsplit` using `[h]`. Conclude with `mul_right_cancel (b := I.ev k b) (by rw [_root_.one_mul]; exact hsplit.symm)`. Introduce `h`. Rewrite using `[hsplit, h, _root_.one_mul]`.

Establish `hrepI : ∀ c, I.ev k (r (π c)) = I.ev k c` using `fun c => by`. Rewrite using `[hIeq]`. Use `modN_neg' (hrep c)` as an intermediate fact. Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis. Establish `hχe : IsUnit (χ e)`.

Apply `he2 Kp χ` to reduce the goal to its premises. Introduce and unpack `(⟨j1, j2⟩ | ⟨o, j⟩)`. Establish `h1 : mχ ≫ w (π (r j1 + r j2)) = mχ ≫ (w j1 * w j2)`. Rewrite using `[MonObj.comp_mul, hmχw, hmχw, hmχw]`. Use `show I.ev k (r (π (r j1 + r j2))) = I.ev k (r j1) * I.ev k (r j2)`.

Rewrite using `[hrepI, I.add]`. Conclude with `congrArg (fun f => f.left) h1`. Establish `h1 : mχ ≫ w (π ((o : 𝓞 E) • r j)) = mχ ≫ (w j ≫ Xo.univ.t.act.act (o : 𝓞 E))`. Rewrite using `[← Category.assoc, hmχw, hmχw]`. Use `show I.ev k (r (π ((o : 𝓞 E) • r j))) = I.ev k (r j) ≫ Xo.univ.t.act.act (o : 𝓞 E)`.

Rewrite using `[hrepI, I.lin]`. Conclude with `congrArg (fun f => f.left) h1`. Introduce and unpack `⟨⟨j1, j2⟩, hj⟩ h`. Apply `hj` to reduce the goal to its premises. Establish `h1 : mχ ≫ w j1 = mχ ≫ w j2` using `Over.OverMorphism.ext h`.

Rewrite `h1` using `[hmχw, hmχw]`. Establish `h2` using `(hIeq _ _).mp h1`. Rewrite using `[← hπr j1, ← hπr j2]`. Conclude with `(hπ _ _).mpr h2`. Use `⟨⟨RingHom.ker (IsLocalization.Away.lift e hχe), RingHom.ker_isPrime (IsLocalization.Away.lift e hχe)⟩, ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Simplify using `only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.mem_ker]`. Rewrite using `[← RingHom.comp_apply, ← RingHom.comp_assoc, IsLocalization.Away.lift_comp, hχφ, hψ, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap κ Kp).injective, Ideal.algebraMap_residueField_eq_zero]`. Introduce `o a`. Use `lin_of_generators Xo.univ.t.act ev hadd hgen ?_ o a` and prove the remaining obligations.

Introduce `o ho a`. Establish `hoa : π (o • a) = π (o • r (π a))`. Rewrite using `[hπ, ← smul_sub]`. Conclude with `modN_smul' o (hrep a)`. Use `show m ≫ w (π (o • a)) = (m ≫ w (π a)) ≫ Xo.univ.t.act.act o`.

Rewrite using `[hoa, Category.assoc]`. Conclude with `heq' (Sum.inr (⟨o, ho⟩, π a))`. Introduce `a`. Rewrite using `[hpow]`. Use `show (m ≫ w (π a)) ^ k = 1`.

Rewrite using `[← MonObj.comp_pow, hw, MonObj.comp_one]`. Introduce `K _ χ a b hab`. Assume the negation of the conclusion as `hnab`. Establish `hne' : π a ≠ π b` using `fun h => hnab ((hπ a b).mp h)`. Establish `hK : IsUnit ((χ.comp alg) e)` using `hunit.map χ`.

Use `(he1 K (χ.comp alg) hK).2 inferInstance ⟨(π a, π b), hne'⟩` as an intermediate fact. Apply `this` to reduce the goal to its premises. Use `show spMap (χ.comp alg) ≫ (w (π a)).left = spMap (χ.comp alg) ≫ (w (π b)).left`. Rewrite using `[spMap_comp_moduli_spaces alg χ, Category.assoc, Category.assoc]`. Conclude with `hab`.
-/
theorem exists_faithfullyFlat_linear_level :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (k : ℕ), 0 < k → ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (ev : Dw.La → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev (k • a) = 1) ∧ ∀ (K : Type) [Field K] (χ : B →+* K) (a b : Dw.La), spMap χ ≫ (ev a).left = spMap χ ≫ (ev b).left → Dw.ModN k (a - b) := by
  intro hL E _ _ _ H Dw l Xo S _ x0 k hk
  classical
  obtain ⟨J, hJ, π, r, hπr, hπ⟩ := exists_finite_quotient Dw k hk
  obtain ⟨B, _, φ, w, hφ, hw, huniv⟩ :=
    exists_flat_universal_torsion_tuple hL E H Dw l Xo S x0 k hk J

  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  have hgen : AddSubgroup.closure (t : Set (𝓞 E)) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, ht]
    simp

  have hrep : ∀ a, Dw.ModN k (a - r (π a)) := fun a => (hπ a (r (π a))).mp (hπr (π a)).symm

  let fa : (J × J) ⊕ (t × J) → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G) :=
    Sum.elim (fun p => w (π (r p.1 + r p.2))) (fun q => w (π ((q.1 : 𝓞 E) • r q.2)))
  let fb : (J × J) ⊕ (t × J) → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G) :=
    Sum.elim (fun p => w p.1 * w p.2) (fun q => w q.2 ≫ Xo.univ.t.act.act (q.1 : 𝓞 E))

  let fc : {p : J × J // p.1 ≠ p.2} → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G) := fun p => w p.1.1
  let fd : {p : J × J // p.1 ≠ p.2} → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G) := fun p => w p.1.2
  have hfa : ∀ i, fa i ^ k = 1 := by
    rintro (p | q) <;> exact hw _
  have hfb : ∀ i, fb i ^ k = 1 := by
    rintro (p | q)
    · show (w p.1 * w p.2) ^ k = 1
      rw [mul_pow, hw, hw, _root_.mul_one]
    · show (w q.2 ≫ Xo.univ.t.act.act (q.1 : 𝓞 E)) ^ k = 1
      have := Xo.univ.t.act.hom (q.1 : 𝓞 E)
      rw [← MonObj.pow_comp, hw, MonObj.one_comp]
  obtain ⟨e, he1, he2⟩ := exists_element hL Xo B (spMap φ ≫ x0) k hk _ _ fa fb fc fd hfa hfb
    (fun p => hw _) (fun p => hw _)
  set B' := Localization.Away e
  set alg := algebraMap B B'
  have halg : spMap alg ≫ (spMap φ ≫ x0) = spMap (alg.comp φ) ≫ x0 := by
    rw [spMap_comp_moduli_spaces φ alg, Category.assoc]
  let m : ptO Xo (spMap (alg.comp φ) ≫ x0) ⟶ ptO Xo (spMap φ ≫ x0) := Over.homMk (spMap alg) halg
  have hm : ∀ f : ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G, (m ≫ f).left = spMap alg ≫ f.left := by
    intro f; rfl
  have hunit : IsUnit (alg e) := IsLocalization.Away.algebraMap_isUnit e
  obtain ⟨heq, hne⟩ := he1 B' alg hunit
  have heq' : ∀ i, m ≫ fa i = m ≫ fb i := fun i =>
    Over.OverMorphism.ext (by rw [hm, hm]; exact heq i)
  let ev : Dw.La → (ptO Xo (spMap (alg.comp φ) ≫ x0) ⟶ Xo.univ.t.G) := fun a => m ≫ w (π a)
  have hadd : ∀ a b, ev (a + b) = ev a * ev b := by
    intro a b
    have hab : π (a + b) = π (r (π a) + r (π b)) := by
      rw [hπ]
      have := modN_add' (hrep a) (hrep b)
      convert this using 1
      abel
    show m ≫ w (π (a + b)) = (m ≫ w (π a)) * (m ≫ w (π b))
    rw [hab, ← MonObj.comp_mul]
    exact heq' (Sum.inl (π a, π b))
  have hev0 : ev 0 = 1 := by
    have h0 := hadd 0 0
    rw [add_zero] at h0
    exact mul_left_cancel (a := ev 0) (by rw [_root_.mul_one]; exact h0.symm)
  have hpow : ∀ (n : ℕ) a, ev (n • a) = ev a ^ n := by
    intro n a
    induction n with
    | zero => rw [zero_smul, pow_zero, hev0]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  refine ⟨B', inferInstance, alg.comp φ, ev, ?_, hadd, ?_, ?_, ?_⟩
  ·
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    refine ⟨RingHom.Flat.comp hφ ?_, ?_⟩
    · exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B' (Submonoid.powers e))
    · intro p
      set κ := p.asIdeal.ResidueField
      set Kp := AlgebraicClosure κ
      set ψ : S →+* Kp := (algebraMap κ Kp).comp (algebraMap S κ) with hψ
      set xp : Sp Kp ⟶ Xo.X := spMap ψ ≫ x0
      have hβ : xp ≫ Xo.s = spMap (Spec.preimage (xp ≫ Xo.s)).hom := by
        simp [spMap]
      obtain ⟨_, I, _, _, _⟩ := Xo.univ.geom Kp xp _ hβ
      let u : J → (ptO Xo (spMap ψ ≫ x0) ⟶ Xo.univ.t.G) := fun j => I.ev k (r j)
      have hu : ∀ j, u j ^ k = 1 := fun j => (I.onto k hk (u j)).mpr ⟨r j, rfl⟩
      obtain ⟨χ, hχφ, hχu⟩ := huniv Kp ψ u hu
      have hmχ : spMap χ ≫ (spMap φ ≫ x0) = spMap ψ ≫ x0 := by
        rw [← hχφ, spMap_comp_moduli_spaces φ χ, Category.assoc]
      let mχ : ptO Xo (spMap ψ ≫ x0) ⟶ ptO Xo (spMap φ ≫ x0) := Over.homMk (spMap χ) hmχ
      have hmχw : ∀ j, mχ ≫ w j = u j := fun j =>
        Over.OverMorphism.ext (by rw [hχu j]; rfl)

      have hIeq : ∀ a b, I.ev k a = I.ev k b ↔ Dw.ModN k (a - b) := by
        intro a b
        have hsplit := I.add k (a - b) b
        rw [sub_add_cancel] at hsplit
        show _ ↔ ∃ c, a - b = k • c
        rw [← I.ker k hk (a - b)]
        constructor
        · intro h
          rw [h] at hsplit
          exact mul_right_cancel (b := I.ev k b) (by rw [_root_.one_mul]; exact hsplit.symm)
        · intro h
          rw [hsplit, h, _root_.one_mul]
      have hrepI : ∀ c, I.ev k (r (π c)) = I.ev k c := fun c => by
        rw [hIeq]
        have := modN_neg' (hrep c)
        rwa [neg_sub] at this
      have hχe : IsUnit (χ e) := by
        apply he2 Kp χ
        · rintro (⟨j1, j2⟩ | ⟨o, j⟩)
          · have h1 : mχ ≫ w (π (r j1 + r j2)) = mχ ≫ (w j1 * w j2) := by
              rw [MonObj.comp_mul, hmχw, hmχw, hmχw]
              show I.ev k (r (π (r j1 + r j2))) = I.ev k (r j1) * I.ev k (r j2)
              rw [hrepI, I.add]
            exact congrArg (fun f => f.left) h1
          · have h1 : mχ ≫ w (π ((o : 𝓞 E) • r j)) =
                mχ ≫ (w j ≫ Xo.univ.t.act.act (o : 𝓞 E)) := by
              rw [← Category.assoc, hmχw, hmχw]
              show I.ev k (r (π ((o : 𝓞 E) • r j))) = I.ev k (r j) ≫ Xo.univ.t.act.act (o : 𝓞 E)
              rw [hrepI, I.lin]
            exact congrArg (fun f => f.left) h1
        · rintro ⟨⟨j1, j2⟩, hj⟩ h
          apply hj
          have h1 : mχ ≫ w j1 = mχ ≫ w j2 := Over.OverMorphism.ext h
          rw [hmχw, hmχw] at h1
          have h2 := (hIeq _ _).mp h1
          rw [← hπr j1, ← hπr j2]
          exact (hπ _ _).mpr h2
      refine ⟨⟨RingHom.ker (IsLocalization.Away.lift e hχe),
        RingHom.ker_isPrime (IsLocalization.Away.lift e hχe)⟩, ?_⟩
      ext x
      simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.mem_ker]
      rw [← RingHom.comp_apply, ← RingHom.comp_assoc, IsLocalization.Away.lift_comp, hχφ, hψ,
        RingHom.comp_apply, map_eq_zero_iff _ (algebraMap κ Kp).injective,
        Ideal.algebraMap_residueField_eq_zero]
  ·
    intro o a
    refine lin_of_generators Xo.univ.t.act ev hadd hgen ?_ o a
    intro o ho a
    have hoa : π (o • a) = π (o • r (π a)) := by
      rw [hπ, ← smul_sub]
      exact modN_smul' o (hrep a)
    show m ≫ w (π (o • a)) = (m ≫ w (π a)) ≫ Xo.univ.t.act.act o
    rw [hoa, Category.assoc]
    exact heq' (Sum.inr (⟨o, ho⟩, π a))
  ·
    intro a
    rw [hpow]
    show (m ≫ w (π a)) ^ k = 1
    rw [← MonObj.comp_pow, hw, MonObj.comp_one]
  ·
    intro K _ χ a b hab
    by_contra hnab
    have hne' : π a ≠ π b := fun h => hnab ((hπ a b).mp h)
    have hK : IsUnit ((χ.comp alg) e) := hunit.map χ
    have := (he1 K (χ.comp alg) hK).2 inferInstance ⟨(π a, π b), hne'⟩
    apply this
    show spMap (χ.comp alg) ≫ (w (π a)).left = spMap (χ.comp alg) ≫ (w (π b)).left
    rw [spMap_comp_moduli_spaces alg χ, Category.assoc, Category.assoc]
    exact hab

end GlobalTheory
