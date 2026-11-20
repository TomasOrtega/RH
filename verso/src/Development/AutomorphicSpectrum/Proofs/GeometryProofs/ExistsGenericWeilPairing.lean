import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingBaseChangeUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.WeilObj

def extPt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) {k : Type} [Field k] (i : Ω →+* k) :
    Over.mk (spMap i ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap i) rfl

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp_of {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
Introduce `K L _ _ i`. Use `haveI : Flat (spMap i) := by`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Use `letI := i.toAlgebra`. Conclude with `RingHom.flat_algebraMap_iff.mpr inferInstance`.

Use `haveI : Surjective (spMap i) := ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩`. Conclude with `Flat.epi_of_flat_of_surjective _`.
-/
theorem epi_spMap_field : ∀ (K L : Type) [Field K] [Field L] (i : K →+* L), Epi (spMap i) := by
  intro K L _ _ i
  haveI : Flat (spMap i) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := i.toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : Surjective (spMap i) := ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

/- English proof (translation)
Introduce `Ω k K _ _ _ i i'`. Use `letI := i.toAlgebra`. Use `letI := i'.toAlgebra`. Use `haveI : Nontrivial (TensorProduct Ω k K) := inferInstance`. Take `⟨m, hm⟩` from `Ideal.exists_maximal (TensorProduct Ω k K)`.

Use `letI : Field (TensorProduct Ω k K ⧸ m) := Ideal.Quotient.field m`. Set `q : TensorProduct Ω k K →+* AlgebraicClosure (TensorProduct Ω k K ⧸ m)` to `(algebraMap _ _).comp (Ideal.Quotient.mk m)`. Use `⟨AlgebraicClosure (TensorProduct Ω k K ⧸ m), inferInstance, inferInstance, q.comp Algebra.TensorProduct.includeLeftRingHom, q.comp (Algebra.TensorProduct.includeRight.toRingHom), ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Simplify using `only [RingHom.comp_apply]`.

Use `congr 1`. Use `show (i a) ⊗ₜ[Ω] (1 : K) = (1 : k) ⊗ₜ[Ω] (i' a)`. Rewrite using `[show i a = a • (1 : k) from (Algebra.algebraMap_eq_smul_one a), show i' a = a • (1 : K) from (Algebra.algebraMap_eq_smul_one a), TensorProduct.smul_tmul]`.
-/
theorem exists_common_closed : ∀ (Ω k K : Type) [Field Ω] [Field k] [Field K] (i : Ω →+* k) (i' : Ω →+* K),
    ∃ (M : Type) (_ : Field M) (_ : IsAlgClosed M) (j : k →+* M) (j' : K →+* M), j.comp i = j'.comp i' := by
  intro Ω k K _ _ _ i i'
  letI := i.toAlgebra
  letI := i'.toAlgebra
  haveI : Nontrivial (TensorProduct Ω k K) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct Ω k K)
  letI : Field (TensorProduct Ω k K ⧸ m) := Ideal.Quotient.field m
  let q : TensorProduct Ω k K →+* AlgebraicClosure (TensorProduct Ω k K ⧸ m) :=
    (algebraMap _ _).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure (TensorProduct Ω k K ⧸ m), inferInstance, inferInstance,
    q.comp Algebra.TensorProduct.includeLeftRingHom, q.comp (Algebra.TensorProduct.includeRight.toRingHom), ?_⟩
  ext a
  simp only [RingHom.comp_apply]
  congr 1
  show (i a) ⊗ₜ[Ω] (1 : K) = (1 : k) ⊗ₜ[Ω] (i' a)
  rw [show i a = a • (1 : k) from (Algebra.algebraMap_eq_smul_one a),
    show i' a = a • (1 : K) from (Algebra.algebraMap_eq_smul_one a), TensorProduct.smul_tmul]

/- English proof (translation)
Introduce `E _ _ _ H D n`. Establish `first : ∀ a : D.La, (∀ c, (n : ℤ) ∣ D.EF a c) → ∃ a', a = n • a'`. Introduce `a h`. Set `ψ : D.La →ₗ[ℤ] ℤ` to `{ toFun := fun c => D.EF a c / n map_add' := fun c c' => by`. Rewrite using `[map_add]`.

Conclude with `Int.add_ediv_of_dvd_left (h c)`. Use the proof step `map_smul' := fun z c => by`. Rewrite using `[map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply]`. Conclude with `Int.mul_ediv_assoc z (h c) }`. Take `⟨a', ha'⟩` from `D.unimod.2 ψ`.

Use `⟨a', D.unimod.1 ?_⟩` and prove the remaining obligations. Use extensionality with `c`. Establish `hc : D.EF (n • a') c = (n : ℤ) * (D.EF a c / n)`. Rewrite using `[map_nsmul, LinearMap.smul_apply, ha', nsmul_eq_mul]`. Both sides reduce to the same expression.

Rewrite using `[hc, Int.mul_ediv_cancel' (h c)]`. Use `⟨first, fun c h => first c fun a => ?_⟩` and prove the remaining obligations. Establish `hs : D.EF c a = - D.EF a c`. Establish `h0` using `D.alt (a + c)`. Simplify using `only [map_add, LinearMap.add_apply, D.alt a, D.alt c, zero_add, add_zero] at h0`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hs]`. Conclude with `(h a).neg_right`.
-/
theorem ef_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n : ℕ),
    (∀ a : D.La, (∀ c, (n : ℤ) ∣ D.EF a c) → ∃ a', a = n • a') ∧
    (∀ c : D.La, (∀ a, (n : ℤ) ∣ D.EF a c) → ∃ c', c = n • c') := by
  intro E _ _ _ H D n
  have first : ∀ a : D.La, (∀ c, (n : ℤ) ∣ D.EF a c) → ∃ a', a = n • a' := by
    intro a h
    let ψ : D.La →ₗ[ℤ] ℤ :=
      { toFun := fun c => D.EF a c / n
        map_add' := fun c c' => by
          rw [map_add]; exact Int.add_ediv_of_dvd_left (h c)
        map_smul' := fun z c => by
          rw [map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply]
          exact Int.mul_ediv_assoc z (h c) }
    obtain ⟨a', ha'⟩ := D.unimod.2 ψ
    refine ⟨a', D.unimod.1 ?_⟩
    ext c
    have hc : D.EF (n • a') c = (n : ℤ) * (D.EF a c / n) := by
      rw [map_nsmul, LinearMap.smul_apply, ha', nsmul_eq_mul]; rfl
    rw [hc, Int.mul_ediv_cancel' (h c)]
  refine ⟨first, fun c h => first c fun a => ?_⟩
  have hs : D.EF c a = - D.EF a c := by
    have h0 := D.alt (a + c)
    simp only [map_add, LinearMap.add_apply, D.alt a, D.alt c, zero_add, add_zero] at h0
    linarith
  rw [hs]; exact (h a).neg_right

/- English proof (translation)
Introduce `E _ _ _ H D Q _ n hn ev hadd hker hon`. Use `haveI : Module.Finite (𝓞 E) D.La := D.fin`. Use `haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La`. Set `φ : D.La →+ Additive Q` to `{ toFun := fun a => Additive.ofMul (ev a) map_zero' := by`. Establish `h` using `hadd 0 0`.

Rewrite `h` using `[add_zero]`. Use `show Additive.ofMul (ev 0) = Additive.ofMul 1`. Use `congr 1`. Conclude with `(mul_eq_left.1 h.symm)`. Use the proof step `map_add' := fun a c => by rw [hadd]; rfl }`.

Set `N : AddSubgroup D.La` to `(nsmulAddMonoidHom (α := D.La) n).range`. Establish `hN : N ≤ φ.ker`. Introduce and unpack `_ ⟨a, rfl⟩`. Use `show Additive.ofMul (ev (n • a)) = 0`. Rewrite using `[hker]`.

Both sides reduce to the same expression. Set `ψ : D.La ⧸ N →+ Additive Q` to `QuotientAddGroup.lift N φ hN`. Use `haveI : AddGroup.FG (D.La ⧸ N) := by haveI : Module.Finite ℤ (D.La ⧸ N.toIntSubmodule) := inferInstance`. Conclude with `(Module.Finite.iff_addGroup_fg).1 this`. Establish `htor : AddMonoid.IsTorsion (D.La ⧸ N)`.

Introduce `q`. Take `⟨a, rfl⟩` from `QuotientAddGroup.mk_surjective q`. Use `(isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨n, hn, ?_⟩` and prove the remaining obligations. Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]`. Conclude with `⟨a, rfl⟩`.

Use `haveI : Finite (D.La ⧸ N) := AddCommGroup.finite_of_fg_torsion _ htor`. Use `Finite.of_surjective (fun q : D.La ⧸ N => (⟨Additive.toMul (ψ q), ?_⟩ : {x : Q // x ^ n = 1})) ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `QuotientAddGroup.mk_surjective q show ev a ^ n = 1`. Establish `: ∀ m : ℕ, ev (m • a) = ev a ^ m`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => rw [zero_smul, pow_zero]`. Conclude with `Additive.ofMul.injective (φ.map_zero)`. Consider the case `succ m ih => rw [succ_nsmul, hadd, ih, pow_succ]`. Rewrite using `[← this, hker]`.

Introduce and unpack `⟨x, hx⟩`. Take `⟨a, rfl⟩` from `hon x hx`. Conclude with `⟨(a : D.La ⧸ N), rfl⟩`.
-/
theorem tors_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Q : Type)
    [Group Q] (n : ℕ), 0 < n → ∀ ev : D.La → Q, (∀ a c, ev (a + c) = ev a * ev c) → (∀ a, ev (n • a) = 1) →
    (∀ x : Q, x ^ n = 1 → ∃ a, ev a = x) → Finite {x : Q // x ^ n = 1} := by
  intro E _ _ _ H D Q _ n hn ev hadd hker hon
  haveI : Module.Finite (𝓞 E) D.La := D.fin
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  let φ : D.La →+ Additive Q :=
    { toFun := fun a => Additive.ofMul (ev a)
      map_zero' := by
        have h := hadd 0 0
        rw [add_zero] at h
        show Additive.ofMul (ev 0) = Additive.ofMul 1
        congr 1
        exact (mul_eq_left.1 h.symm)
      map_add' := fun a c => by rw [hadd]; rfl }
  let N : AddSubgroup D.La := (nsmulAddMonoidHom (α := D.La) n).range
  have hN : N ≤ φ.ker := by
    rintro _ ⟨a, rfl⟩
    show Additive.ofMul (ev (n • a)) = 0
    rw [hker]; rfl
  let ψ : D.La ⧸ N →+ Additive Q := QuotientAddGroup.lift N φ hN
  haveI : AddGroup.FG (D.La ⧸ N) := by
    haveI : Module.Finite ℤ (D.La ⧸ N.toIntSubmodule) := inferInstance
    exact (Module.Finite.iff_addGroup_fg).1 this
  have htor : AddMonoid.IsTorsion (D.La ⧸ N) := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine (isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨n, hn, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨a, rfl⟩
  haveI : Finite (D.La ⧸ N) := AddCommGroup.finite_of_fg_torsion _ htor
  refine Finite.of_surjective (fun q : D.La ⧸ N => (⟨Additive.toMul (ψ q), ?_⟩ : {x : Q // x ^ n = 1})) ?_
  · obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    show ev a ^ n = 1
    have : ∀ m : ℕ, ev (m • a) = ev a ^ m := by
      intro m
      induction m with
      | zero => rw [zero_smul, pow_zero]; exact Additive.ofMul.injective (φ.map_zero)
      | succ m ih => rw [succ_nsmul, hadd, ih, pow_succ]
    rw [← this, hker]
  · rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := hon x hx
    exact ⟨(a : D.La ⧸ N), rfl⟩

/- English proof (translation)
Introduce `E _ _ _ H D l B _ b S X s o t f m Ω _ ξ₀ k _ _ i n hn`. It suffices to establish `key : ∀ q : Sp k ⟶ X, q = (spMap i ≫ ξ₀) ≫ f → ∃ (ζk : kˣ) (ev : D.La → (Over.mk q ⟶ t.G)), IsPrimitiveRoot ζk n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a = 1 ↔ ∃ c, a = n • c) ∧ (∀ x, x ^ n = 1 ↔ ∃ a, ev a = x) ∧ ∀ a c, Out.WeilIs t.G t.PP.L n (ev a) (ev c) (unitOn (ζk ^ …`. Introduce `q hq`. Substitute `hq` using the available equality. Set `β₀ : B →+* Ω` to `(Spec.preimage (ξ₀ ≫ s)).hom`.

Establish `h1 : spMap β₀ = ξ₀ ≫ s`. Simplify using `only [β₀, spMap, CommRingCat.ofHom_hom, Spec.map_preimage]`. Establish `hβ : (spMap i ≫ ξ₀) ≫ s = spMap (i.comp β₀)`. Rewrite using `[Category.assoc, spMap_comp_of, h1]`. Take `⟨-, I, -, -, -⟩` from `o.geom k (spMap i ≫ ξ₀) (i.comp β₀) hβ`.

Take `⟨w, hw, -, -⟩` from `(isPullCubical_iff m.cm t.cub o.t.cub).1 m.lin`. Establish `hLB : LBIso o.t.PP.L (t.PP.L.pull m.cm.F)` using `⟨w, (isGen_iff w).2 hw⟩`. Establish `hp : IsGrpPullback o.t.G t.G f m.cm.F` using `m.cart`. Set `T : Over S` to `Over.mk (spMap i ≫ ξ₀)`. Set `P` to `pushHom hp T`.

Establish `hinj : Function.Injective P` using `fun x y hxy => Over.OverMorphism.ext (hp.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y]))`. Establish `hsurj : Function.Surjective P` using `fun x₀ => ⟨Over.homMk (hp.1.lift x₀.left T.hom (Over.w x₀)) (hp.1.lift_snd _ _ _), Over.OverMorphism.ext (hp.1.lift_fst _ _ _)⟩`. Use `⟨I.ζ n, fun a => P (I.ev n a), I.ζ_prim n hn, fun a c => by show P (I.ev n (a + c)) = P (I.ev n a) * P (I.ev n c)` and prove the remaining obligations. Rewrite using `[I.add, map_mul],`. Use `fun a => (map_eq_one_iff P hinj).trans (I.ker n hn a), fun x => ?_, fun a c => ?_⟩`.

Take `⟨y, rfl⟩` from `hsurj x`. Rewrite using `[← map_pow, map_eq_one_iff P hinj, I.onto n hn]`. Conclude with `exists_congr fun a => hinj.eq_iff.symm`. Establish `h : Out.WeilIs o.t.G o.t.PP.L n (I.ev n a) (I.ev n c) (unitOn (I.ζ n ^ D.EF a c))` using `I.isom n hn a c`. Conclude with `(GlobalTheory.weilIs_grpPullback_of_comm' X S t.G o.t.G f m.cm.F t.PP.L o.t.PP.L t.PP.isLB o.t.PP.isLB hp hLB T n (I.ev n a) (I.ev n c) (P (I.ev n a)) (P (I.ev n c)) _ rfl rfl).1 h`.
-/
theorem obj_tate_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (B : Type) [CommRing B] (b : Base l B) (S X : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (t : SAB H X)
    (f : S ⟶ X) (_ : SABMap o.t t f) (Ω : Type) [Field Ω] (ξ₀ : Sp Ω ⟶ S) (k : Type) [Field k] [IsAlgClosed k]
    (i : Ω →+* k) (n : ℕ), 0 < n → ∃ (ζk : kˣ) (ev : D.La → (Over.mk (spMap i ≫ ξ₀ ≫ f) ⟶ t.G)),
      IsPrimitiveRoot ζk n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a = 1 ↔ ∃ c, a = n • c) ∧
      (∀ x, x ^ n = 1 ↔ ∃ a, ev a = x) ∧
      ∀ a c, Out.WeilIs t.G t.PP.L n (ev a) (ev c) (unitOn (ζk ^ D.EF a c)) := by
  intro E _ _ _ H D l B _ b S X s o t f m Ω _ ξ₀ k _ _ i n hn
  suffices key : ∀ q : Sp k ⟶ X, q = (spMap i ≫ ξ₀) ≫ f → ∃ (ζk : kˣ) (ev : D.La → (Over.mk q ⟶ t.G)),
      IsPrimitiveRoot ζk n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a = 1 ↔ ∃ c, a = n • c) ∧
      (∀ x, x ^ n = 1 ↔ ∃ a, ev a = x) ∧
      ∀ a c, Out.WeilIs t.G t.PP.L n (ev a) (ev c) (unitOn (ζk ^ D.EF a c)) from
    key _ (Category.assoc _ _ _).symm
  intro q hq
  subst hq
  let β₀ : B →+* Ω := (Spec.preimage (ξ₀ ≫ s)).hom
  have h1 : spMap β₀ = ξ₀ ≫ s := by
    simp only [β₀, spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hβ : (spMap i ≫ ξ₀) ≫ s = spMap (i.comp β₀) := by
    rw [Category.assoc, spMap_comp_of, h1]
  obtain ⟨-, I, -, -, -⟩ := o.geom k (spMap i ≫ ξ₀) (i.comp β₀) hβ
  obtain ⟨w, hw, -, -⟩ := (isPullCubical_iff m.cm t.cub o.t.cub).1 m.lin
  have hLB : LBIso o.t.PP.L (t.PP.L.pull m.cm.F) := ⟨w, (isGen_iff w).2 hw⟩
  have hp : IsGrpPullback o.t.G t.G f m.cm.F := m.cart
  let T : Over S := Over.mk (spMap i ≫ ξ₀)
  let P := pushHom hp T
  have hinj : Function.Injective P := fun x y hxy =>
    Over.OverMorphism.ext (hp.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y]))
  have hsurj : Function.Surjective P := fun x₀ =>
    ⟨Over.homMk (hp.1.lift x₀.left T.hom (Over.w x₀)) (hp.1.lift_snd _ _ _),
      Over.OverMorphism.ext (hp.1.lift_fst _ _ _)⟩
  refine ⟨I.ζ n, fun a => P (I.ev n a), I.ζ_prim n hn, fun a c => by
      show P (I.ev n (a + c)) = P (I.ev n a) * P (I.ev n c)
      rw [I.add, map_mul],
    fun a => (map_eq_one_iff P hinj).trans (I.ker n hn a), fun x => ?_, fun a c => ?_⟩
  · obtain ⟨y, rfl⟩ := hsurj x
    rw [← map_pow, map_eq_one_iff P hinj, I.onto n hn]
    exact exists_congr fun a => hinj.eq_iff.symm
  · have h : Out.WeilIs o.t.G o.t.PP.L n (I.ev n a) (I.ev n c) (unitOn (I.ζ n ^ D.EF a c)) := I.isom n hn a c
    exact (GlobalTheory.weilIs_grpPullback_of_comm' X S t.G o.t.G f m.cm.F t.PP.L o.t.PP.L t.PP.isLB o.t.PP.isLB hp hLB T n
      (I.ev n a) (I.ev n c) (P (I.ev n a)) (P (I.ev n c)) _ rfl rfl).1 h

/- English proof (translation)
Introduce `_ E _ _ _ H D l B _ b S X s o t f m Ω _ _ ξ₀ n hn hFT hζ`. Take `⟨ζ, hζ⟩` from `hζ`. Establish `hn0 : 0 < n` using `hn`. Use `haveI : NeZero n := ⟨by omega⟩`. Establish `hL : t.PP.L.IsLB` using `t.PP.isLB`.

Set `K` to `AlgebraicClosure Ω`. Set `iK : Ω →+* K` to `algebraMap Ω K`. Use `haveI : CharZero K := charZero_of_injective_algebraMap iK.injective`. Use `haveI : Epi (spMap iK) := epi_spMap_field Ω K iK`. Establish `tors : ∀ {k : Type} [Field k] (i : Ω →+* k) (x : Over.mk (ξ₀ ≫ f) ⟶ t.G), x ^ n = 1 → (extPt (ξ₀ ≫ f) i ≫ x) ^ n = 1` using `fun i x hx => by rw [← MonObj.comp_pow, hx, MonObj.comp_one]`.

Establish `inj : ∀ x x' : Over.mk (ξ₀ ≫ f) ⟶ t.G, extPt (ξ₀ ≫ f) iK ≫ x = extPt (ξ₀ ≫ f) iK ≫ x' → x = x'` using `fun x x' h => by`. Establish `h' : spMap iK ≫ x.left = spMap iK ≫ x'.left` using `congrArg CommaMorphism.left h`. Conclude with `Over.OverMorphism.ext ((cancel_epi (spMap iK)).1 h')`. Establish `geo` using `obj_tate_at E H D l B b S X s o t f m Ω ξ₀`. Establish `exk : ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (xk gk : Over.mk (spMap i ≫ ξ₀ ≫ f) ⟶ t.G), xk ^ n = 1 → gk ^ n = 1 → ∃ c : kˣ, c ^ n = 1 ∧ Out.WeilIs t.G t.PP.L n xk gk (unitOn c)`.

Introduce `k _ _ i xk gk hx hg`. Take `⟨ζk, ev, hp, -, -, hon, hw⟩` from `geo k i n hn0`. Take `⟨a, rfl⟩` from `(hon xk).1 hx`. Take `⟨c, rfl⟩` from `(hon gk).1 hg`. Use `⟨ζk ^ D.EF a c, ?_, hw a c⟩` and prove the remaining obligations.

Rewrite using `[← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp.pow_eq_one, one_zpow]`. Establish `valK : ∀ x g : Over.mk (ξ₀ ≫ f) ⟶ t.G, ∃ u : Ωˣ, x ^ n = 1 → g ^ n = 1 → Out.WeilIs t.G t.PP.L n (extPt (ξ₀ ≫ f) iK ≫ x) (extPt (ξ₀ ≫ f) iK ≫ g) (unitOn (Units.map iK.toMonoidHom u))`. Introduce `x g`. Distinguish the cases in `h : x ^ n = 1 ∧ g ^ n = 1`. Take `⟨c, hc, hw⟩` from `exk K iK _ _ (tors iK x h.1) (tors iK g h.2)`.

Establish `hζK : IsPrimitiveRoot (iK ζ) n` using `hζ.map_of_injective iK.injective`. Take `⟨j, -, hj⟩` from `hζK.eq_pow_of_pow_eq_one (ξ := (c : K)) (by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one])`. Establish `hne : ζ ^ j ≠ 0` using `pow_ne_zero _ (hζ.ne_zero (by omega))`. Use `⟨Units.mk0 (ζ ^ j) hne, fun _ _ => ?_⟩` and prove the remaining obligations. Establish `: Units.map iK.toMonoidHom (Units.mk0 (ζ ^ j) hne) = c` using `by ext; simp [← hj]`.

Rewrite using `[this]`. Conclude with `hw`. Conclude with `⟨1, fun a b => (h ⟨a, b⟩).elim⟩`. Use `choose e he using valK`. Establish `char : ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (x g : Over.mk (ξ₀ ≫ f) ⟶ t.G), x ^ n = 1 → g ^ n = 1 → ∀ (xk gk : Over.mk (spMap i ≫ ξ₀ ≫ f) ⟶ t.G) (c : kˣ), xk.left = spMap i ≫ x.left → gk.left = spMap i ≫ g.left → Out.WeilIs t.G t.PP.L n xk gk (unitOn c) → c = Unit …`.

Introduce `k _ _ i x g hx hg xk gk c hxk hgk hc`. Take `⟨M, _, _, j, j', hjj⟩` from `exists_common_closed Ω k K i iK`. Establish `hq : spMap (j.comp i) ≫ ξ₀ ≫ f = spMap j ≫ spMap i ≫ ξ₀ ≫ f`. Rewrite using `[spMap_comp_of, Category.assoc]`. Establish `hq' : spMap (j.comp i) ≫ ξ₀ ≫ f = spMap j' ≫ spMap iK ≫ ξ₀ ≫ f`.

Rewrite using `[hjj, spMap_comp_of, Category.assoc]`. Take `⟨cM, -, hcM⟩` from `exk M (j.comp i) (extPt (ξ₀ ≫ f) (j.comp i) ≫ x) (extPt (ξ₀ ≫ f) (j.comp i) ≫ g) (tors _ x hx) (tors _ g hg)`. Establish `e1` using `GlobalTheory.T.weil_pairing_base_change_unit t.G t.PP.L hL k M j _ _ hq n xk gk (extPt (ξ₀ ≫ f) (j.comp i) ≫ x) (extPt (ξ₀ ≫ f) (j.comp i) ≫ g) (show spMap (j.comp i) ≫ x.left = spMap j ≫ xk.left by rw [hxk, spMap_comp_of, Category.assoc]) (show spMap (j.comp i) ≫ g.left = spMap …`. Establish `e2` using `GlobalTheory.T.weil_pairing_base_change_unit t.G t.PP.L hL K M j' _ _ hq' n (extPt (ξ₀ ≫ f) iK ≫ x) (extPt (ξ₀ ≫ f) iK ≫ g) (extPt (ξ₀ ≫ f) (j.comp i) ≫ x) (extPt (ξ₀ ≫ f) (j.comp i) ≫ g) (show spMap (j.comp i) ≫ x.left = spMap j' ≫ (spMap iK ≫ x.left) by`. Rewrite using `[hjj, spMap_comp_of, Category.assoc])`.

Use the proof step `(show spMap (j.comp i) ≫ g.left = spMap j' ≫ (spMap iK ≫ g.left) by`. Rewrite using `[hjj, spMap_comp_of, Category.assoc]) _ cM (he x g hx hg) hcM`. Establish `h3` using `congrArg Units.val (e1.symm.trans e2)`. Simplify using `only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h3`. Apply `Units.ext` to reduce the goal to its premises.

Apply `j.injective` to reduce the goal to its premises. Rewrite using `[h3]`. Simplify using `only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]`. Conclude with `(RingHom.congr_fun hjj _).symm`. Establish `hweil : ∀ x g, x ^ n = 1 → g ^ n = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (xk gk : Over.mk (spMap i ≫ ξ₀ ≫ f) ⟶ t.G) (c : kˣ), xk.left = spMap i ≫ x.left → gk.left = spMap i ≫ g.left → (Out.WeilIs t.G t.PP.L n xk gk (unitOn c) ↔ (c : k) = i (e x g))`.

Introduce `x g hx hg k _ _ i xk gk c hxk hgk`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[char k i x g hx hg xk gk c hxk hgk h]`. Both sides reduce to the same expression.

Introduce `h`. Establish `hxk' : xk = extPt _ i ≫ x` using `Over.OverMorphism.ext hxk`. Establish `hgk' : gk = extPt _ i ≫ g` using `Over.OverMorphism.ext hgk`. Take `⟨c0, -, h0⟩` from `exk k i xk gk (by rw [hxk']; exact tors i x hx) (by rw [hgk']; exact tors i g hg)`. Establish `h1` using `char k i x g hx hg xk gk c0 hxk hgk h0`.

Establish `hc : c = c0`. Rewrite using `[h1]; exact Units.ext (by rw [h]; rfl)`. Rewrite using `[hc]`. Conclude with `h0`. Take `⟨ζK, ev, hpK, hadd, hker, hon, hwK⟩` from `geo K iK n hn0`.

Establish `lift : ∀ a, ∃ x : Over.mk (ξ₀ ≫ f) ⟶ t.G, x ^ n = 1 ∧ extPt _ iK ≫ x = ev a`. Introduce `a`. Establish `ht : (ev a) ^ n = 1` using `(hon _).2 ⟨a, rfl⟩`. Take `⟨x, hx⟩` from `hFT K iK (ev a) ht`. Establish `hxe : extPt _ iK ≫ x = ev a` using `Over.OverMorphism.ext hx.symm`.

Use `⟨x, inj _ _ ?_, hxe⟩` and prove the remaining obligations. Rewrite using `[MonObj.comp_pow, hxe, ht, MonObj.comp_one]`. Establish `val : ∀ x g, x ^ n = 1 → g ^ n = 1 → ∀ a c, ev a = extPt _ iK ≫ x → ev c = extPt _ iK ≫ g → ζK ^ D.EF a c = Units.map iK.toMonoidHom (e x g)` using `fun x g hx hg a c ha hc => char K iK x g hx hg (ev a) (ev c) _ (by rw [ha]; rfl) (by rw [hc]; rfl) (hwK a c)`. Establish `coord : ∀ x : Over.mk (ξ₀ ≫ f) ⟶ t.G, x ^ n = 1 → ∃ a, ev a = extPt _ iK ≫ x` using `fun x hx => (hon _).1 (tors iK x hx)`. Establish `hl : ∀ x x' g, x ^ n = 1 → x' ^ n = 1 → g ^ n = 1 → e (x * x') g = e x g * e x' g`.

Introduce `x x' g hx hx' hg`. Take `⟨a, ha⟩` from `coord x hx`. Take `⟨a', ha'⟩` from `coord x' hx'`. Take `⟨c, hc⟩` from `coord g hg`. Establish `hxx : (x * x') ^ n = 1` using `by rw [mul_pow, hx, hx', _root_.one_mul]`.

Establish `h1` using `val _ _ hxx hg (a + a') c (by rw [hadd, ha, ha', MonObj.comp_mul]) hc`. Establish `h2` using `val _ _ hx hg a c ha hc`. Establish `h3` using `val _ _ hx' hg a' c ha' hc`. Apply `Units.map_injective (f := iK.toMonoidHom) iK.injective` to reduce the goal to its premises. Rewrite using `[map_mul, ← h1, ← h2, ← h3, map_add, LinearMap.add_apply, zpow_add]`.

Establish `hr : ∀ x g g', x ^ n = 1 → g ^ n = 1 → g' ^ n = 1 → e x (g * g') = e x g * e x g'`. Introduce `x g g' hx hg hg'`. Take `⟨a, ha⟩` from `coord x hx`. Take `⟨c, hc⟩` from `coord g hg`. Take `⟨c', hc'⟩` from `coord g' hg'`.

Establish `hgg : (g * g') ^ n = 1` using `by rw [mul_pow, hg, hg', _root_.one_mul]`. Establish `h1` using `val _ _ hx hgg a (c + c') ha (by rw [hadd, hc, hc', MonObj.comp_mul])`. Establish `h2` using `val _ _ hx hg a c ha hc`. Establish `h3` using `val _ _ hx hg' a c' ha hc'`. Apply `Units.map_injective (f := iK.toMonoidHom) iK.injective` to reduce the goal to its premises.

Rewrite using `[map_mul, ← h1, ← h2, ← h3, map_add, zpow_add]`. Establish `hL4` using `ef_dvd E H D n`. Establish `zeroOf : ∀ a c, ζK ^ D.EF a c = 1 → (n : ℤ) ∣ D.EF a c` using `fun a c h => (hpK.zpow_eq_one_iff_dvd _).1 h`. Establish `nondegR : ∀ g, g ^ n = 1 → (∀ x, x ^ n = 1 → e x g = 1) → g = 1`. Introduce `g hg h`.

Take `⟨c, hc⟩` from `coord g hg`. Take `⟨c', rfl⟩` from `hL4.2 c fun a => by`. Take `⟨x, hx, hxa⟩` from `lift a`. Apply `zeroOf` to reduce the goal to its premises. Rewrite using `[val x g hx hg a _ hxa.symm hc, h x hx, map_one]`.

Apply `inj` to reduce the goal to its premises. Rewrite using `[MonObj.comp_one, ← hc]`. Conclude with `(hker _).2 ⟨c', rfl⟩`. Establish `nondegL : ∀ x, x ^ n = 1 → (∀ g, g ^ n = 1 → e x g = 1) → x = 1`. Introduce `x hx h`.

Take `⟨a, ha⟩` from `coord x hx`. Take `⟨a', rfl⟩` from `hL4.1 a fun c => by`. Take `⟨g, hg, hgc⟩` from `lift c`. Apply `zeroOf` to reduce the goal to its premises. Rewrite using `[val x g hx hg _ c ha hgc.symm, h g hg, map_one]`.

Apply `inj` to reduce the goal to its premises. Rewrite using `[MonObj.comp_one, ← ha]`. Conclude with `(hker _).2 ⟨a', rfl⟩`. Establish `finK : Finite {y : Over.mk (spMap iK ≫ ξ₀ ≫ f) ⟶ t.G // y ^ n = 1}` using `tors_finite E H D _ n hn0 ev hadd (fun a => (hker _).2 ⟨a, rfl⟩) (fun y hy => (hon y).1 hy)`. Establish `hfin : Finite {x : Over.mk (ξ₀ ≫ f) ⟶ t.G // x ^ n = 1}` using `Finite.of_injective (fun x => (⟨extPt _ iK ≫ x.1, tors iK x.1 x.2⟩ : {y : Over.mk (spMap iK ≫ ξ₀ ≫ f) ⟶ t.G // y ^ n = 1})) (fun x x' h => Subtype.ext (inj _ _ (congrArg Subtype.val h)))`.

Use `⟨e, hfin, hl, hr, ?_, nondegR, hweil⟩` and prove the remaining obligations. Introduce `χ hχ`. Set `T : Subgroup (Over.mk (ξ₀ ≫ f) ⟶ t.G)` to `(powMonoidHom n).ker`. Use `haveI : Finite T := hfin`. Set `ch : T → (T →* Kˣ)` to `fun x => MonoidHom.mk' (fun g => Units.map iK.toMonoidHom (e x g)) fun g g' => by show Units.map iK.toMonoidHom (e x (g * g')) = _`.

Rewrite using `[hr _ _ _ x.2 g.2 g'.2, map_mul]`. Set `Φ : T →* (T →* Kˣ)` to `MonoidHom.mk' ch fun x x' => by`. Use extensionality with `g : 1`. Use `show Units.map iK.toMonoidHom (e ((x : Over.mk (ξ₀ ≫ f) ⟶ t.G) * x') g) = Units.map iK.toMonoidHom (e x g) * Units.map iK.toMonoidHom (e x' g)`. Rewrite using `[← map_mul, hl _ _ _ x.2 x'.2 g.2]`.

Establish `hinj : Function.Injective Φ` using `(injective_iff_map_eq_one Φ).2 fun x hx => Subtype.ext (nondegL x x.2 fun g hg => by`. Establish `h1 : Units.map iK.toMonoidHom (e x g) = 1` using `DFunLike.congr_fun hx ⟨g, hg⟩`. Conclude with `Units.map_injective (f := iK.toMonoidHom) iK.injective (h1.trans (map_one _).symm))`. Use `haveI : NeZero ((Monoid.exponent T : ℕ) : K) := ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩`. Establish `hcard` using `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity T K`.

Use `haveI : Finite (T →* Kˣ) := Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')`. Establish `hbij` using `hinj.bijective_of_nat_card_le hcard.le`. Take `⟨x, hx⟩` from `hbij.2 (MonoidHom.mk' (fun g : T => Units.map iK.toMonoidHom (χ g)) fun g g' => by show Units.map iK.toMonoidHom (χ ((g : Over.mk (ξ₀ ≫ f) ⟶ t.G) * g')) = _`. Rewrite using `[hχ _ _ g.2 g'.2, map_mul])`. Conclude with `⟨x, x.2, fun g hg => Units.map_injective (f := iK.toMonoidHom) iK.injective (DFunLike.congr_fun hx ⟨g, hg⟩).symm⟩`.
-/
theorem genWeil_of_obj : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S X : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (f : S ⟶ X) (_ : SABMap o.t t f) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ S) (n : ℕ), 1 ≤ n → FullTorsion t.G (ξ₀ ≫ f) n → (∃ ζ : Ω, IsPrimitiveRoot ζ n) → ∃ e, GenWeil t.G t.PP.L (ξ₀ ≫ f) n e := by
  intro _ E _ _ _ H D l B _ b S X s o t f m Ω _ _ ξ₀ n hn hFT hζ
  obtain ⟨ζ, hζ⟩ := hζ
  classical
  have hn0 : 0 < n := hn
  haveI : NeZero n := ⟨by omega⟩
  have hL : t.PP.L.IsLB := t.PP.isLB
  let K := AlgebraicClosure Ω
  let iK : Ω →+* K := algebraMap Ω K
  haveI : CharZero K := charZero_of_injective_algebraMap iK.injective
  haveI : Epi (spMap iK) := epi_spMap_field Ω K iK
  have tors : ∀ {k : Type} [Field k] (i : Ω →+* k) (x : Over.mk (ξ₀ ≫ f) ⟶ t.G), x ^ n = 1 →
      (extPt (ξ₀ ≫ f) i ≫ x) ^ n = 1 := fun i x hx => by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have inj : ∀ x x' : Over.mk (ξ₀ ≫ f) ⟶ t.G, extPt (ξ₀ ≫ f) iK ≫ x = extPt (ξ₀ ≫ f) iK ≫ x' → x = x' :=
    fun x x' h => by
      have h' : spMap iK ≫ x.left = spMap iK ≫ x'.left := congrArg CommaMorphism.left h
      exact Over.OverMorphism.ext ((cancel_epi (spMap iK)).1 h')
  have geo := obj_tate_at E H D l B b S X s o t f m Ω ξ₀
  have exk : ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (xk gk : Over.mk (spMap i ≫ ξ₀ ≫ f) ⟶ t.G),
      xk ^ n = 1 → gk ^ n = 1 → ∃ c : kˣ, c ^ n = 1 ∧ Out.WeilIs t.G t.PP.L n xk gk (unitOn c) := by
    intro k _ _ i xk gk hx hg
    obtain ⟨ζk, ev, hp, -, -, hon, hw⟩ := geo k i n hn0
    obtain ⟨a, rfl⟩ := (hon xk).1 hx
    obtain ⟨c, rfl⟩ := (hon gk).1 hg
    refine ⟨ζk ^ D.EF a c, ?_, hw a c⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp.pow_eq_one, one_zpow]
  have valK : ∀ x g : Over.mk (ξ₀ ≫ f) ⟶ t.G, ∃ u : Ωˣ, x ^ n = 1 → g ^ n = 1 →
      Out.WeilIs t.G t.PP.L n (extPt (ξ₀ ≫ f) iK ≫ x) (extPt (ξ₀ ≫ f) iK ≫ g)
        (unitOn (Units.map iK.toMonoidHom u)) := by
    intro x g
    by_cases h : x ^ n = 1 ∧ g ^ n = 1
    · obtain ⟨c, hc, hw⟩ := exk K iK _ _ (tors iK x h.1) (tors iK g h.2)
      have hζK : IsPrimitiveRoot (iK ζ) n := hζ.map_of_injective iK.injective
      obtain ⟨j, -, hj⟩ := hζK.eq_pow_of_pow_eq_one (ξ := (c : K))
        (by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one])
      have hne : ζ ^ j ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by omega))
      refine ⟨Units.mk0 (ζ ^ j) hne, fun _ _ => ?_⟩
      have : Units.map iK.toMonoidHom (Units.mk0 (ζ ^ j) hne) = c := by
        ext; simp [← hj]
      rw [this]; exact hw
    · exact ⟨1, fun a b => (h ⟨a, b⟩).elim⟩
  choose e he using valK
  have char : ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (x g : Over.mk (ξ₀ ≫ f) ⟶ t.G), x ^ n = 1 →
      g ^ n = 1 → ∀ (xk gk : Over.mk (spMap i ≫ ξ₀ ≫ f) ⟶ t.G) (c : kˣ), xk.left = spMap i ≫ x.left →
      gk.left = spMap i ≫ g.left → Out.WeilIs t.G t.PP.L n xk gk (unitOn c) →
      c = Units.map i.toMonoidHom (e x g) := by
    intro k _ _ i x g hx hg xk gk c hxk hgk hc
    obtain ⟨M, _, _, j, j', hjj⟩ := exists_common_closed Ω k K i iK
    have hq : spMap (j.comp i) ≫ ξ₀ ≫ f = spMap j ≫ spMap i ≫ ξ₀ ≫ f := by
      rw [spMap_comp_of, Category.assoc]
    have hq' : spMap (j.comp i) ≫ ξ₀ ≫ f = spMap j' ≫ spMap iK ≫ ξ₀ ≫ f := by
      rw [hjj, spMap_comp_of, Category.assoc]
    obtain ⟨cM, -, hcM⟩ := exk M (j.comp i) (extPt (ξ₀ ≫ f) (j.comp i) ≫ x) (extPt (ξ₀ ≫ f) (j.comp i) ≫ g)
      (tors _ x hx) (tors _ g hg)
    have e1 := GlobalTheory.T.weil_pairing_base_change_unit t.G t.PP.L hL k M j _ _ hq n xk gk (extPt (ξ₀ ≫ f) (j.comp i) ≫ x)
      (extPt (ξ₀ ≫ f) (j.comp i) ≫ g)
      (show spMap (j.comp i) ≫ x.left = spMap j ≫ xk.left by rw [hxk, spMap_comp_of, Category.assoc])
      (show spMap (j.comp i) ≫ g.left = spMap j ≫ gk.left by rw [hgk, spMap_comp_of, Category.assoc]) c cM hc hcM
    have e2 := GlobalTheory.T.weil_pairing_base_change_unit t.G t.PP.L hL K M j' _ _ hq' n (extPt (ξ₀ ≫ f) iK ≫ x) (extPt (ξ₀ ≫ f) iK ≫ g)
      (extPt (ξ₀ ≫ f) (j.comp i) ≫ x) (extPt (ξ₀ ≫ f) (j.comp i) ≫ g)
      (show spMap (j.comp i) ≫ x.left = spMap j' ≫ (spMap iK ≫ x.left) by
        rw [hjj, spMap_comp_of, Category.assoc])
      (show spMap (j.comp i) ≫ g.left = spMap j' ≫ (spMap iK ≫ g.left) by
        rw [hjj, spMap_comp_of, Category.assoc]) _ cM (he x g hx hg) hcM
    have h3 := congrArg Units.val (e1.symm.trans e2)
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h3
    apply Units.ext
    apply j.injective
    rw [h3]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    exact (RingHom.congr_fun hjj _).symm
  have hweil : ∀ x g, x ^ n = 1 → g ^ n = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k)
      (xk gk : Over.mk (spMap i ≫ ξ₀ ≫ f) ⟶ t.G) (c : kˣ), xk.left = spMap i ≫ x.left →
      gk.left = spMap i ≫ g.left → (Out.WeilIs t.G t.PP.L n xk gk (unitOn c) ↔ (c : k) = i (e x g)) := by
    intro x g hx hg k _ _ i xk gk c hxk hgk
    constructor
    · intro h
      rw [char k i x g hx hg xk gk c hxk hgk h]
      rfl
    · intro h
      have hxk' : xk = extPt _ i ≫ x := Over.OverMorphism.ext hxk
      have hgk' : gk = extPt _ i ≫ g := Over.OverMorphism.ext hgk
      obtain ⟨c0, -, h0⟩ := exk k i xk gk (by rw [hxk']; exact tors i x hx) (by rw [hgk']; exact tors i g hg)
      have h1 := char k i x g hx hg xk gk c0 hxk hgk h0
      have hc : c = c0 := by
        rw [h1]; exact Units.ext (by rw [h]; rfl)
      rw [hc]; exact h0
  obtain ⟨ζK, ev, hpK, hadd, hker, hon, hwK⟩ := geo K iK n hn0
  have lift : ∀ a, ∃ x : Over.mk (ξ₀ ≫ f) ⟶ t.G, x ^ n = 1 ∧ extPt _ iK ≫ x = ev a := by
    intro a
    have ht : (ev a) ^ n = 1 := (hon _).2 ⟨a, rfl⟩
    obtain ⟨x, hx⟩ := hFT K iK (ev a) ht
    have hxe : extPt _ iK ≫ x = ev a := Over.OverMorphism.ext hx.symm
    refine ⟨x, inj _ _ ?_, hxe⟩
    rw [MonObj.comp_pow, hxe, ht, MonObj.comp_one]
  have val : ∀ x g, x ^ n = 1 → g ^ n = 1 → ∀ a c, ev a = extPt _ iK ≫ x → ev c = extPt _ iK ≫ g →
      ζK ^ D.EF a c = Units.map iK.toMonoidHom (e x g) := fun x g hx hg a c ha hc =>
    char K iK x g hx hg (ev a) (ev c) _ (by rw [ha]; rfl) (by rw [hc]; rfl) (hwK a c)
  have coord : ∀ x : Over.mk (ξ₀ ≫ f) ⟶ t.G, x ^ n = 1 → ∃ a, ev a = extPt _ iK ≫ x :=
    fun x hx => (hon _).1 (tors iK x hx)
  have hl : ∀ x x' g, x ^ n = 1 → x' ^ n = 1 → g ^ n = 1 → e (x * x') g = e x g * e x' g := by
    intro x x' g hx hx' hg
    obtain ⟨a, ha⟩ := coord x hx
    obtain ⟨a', ha'⟩ := coord x' hx'
    obtain ⟨c, hc⟩ := coord g hg
    have hxx : (x * x') ^ n = 1 := by rw [mul_pow, hx, hx', _root_.one_mul]
    have h1 := val _ _ hxx hg (a + a') c (by rw [hadd, ha, ha', MonObj.comp_mul]) hc
    have h2 := val _ _ hx hg a c ha hc
    have h3 := val _ _ hx' hg a' c ha' hc
    apply Units.map_injective (f := iK.toMonoidHom) iK.injective
    rw [map_mul, ← h1, ← h2, ← h3, map_add, LinearMap.add_apply, zpow_add]
  have hr : ∀ x g g', x ^ n = 1 → g ^ n = 1 → g' ^ n = 1 → e x (g * g') = e x g * e x g' := by
    intro x g g' hx hg hg'
    obtain ⟨a, ha⟩ := coord x hx
    obtain ⟨c, hc⟩ := coord g hg
    obtain ⟨c', hc'⟩ := coord g' hg'
    have hgg : (g * g') ^ n = 1 := by rw [mul_pow, hg, hg', _root_.one_mul]
    have h1 := val _ _ hx hgg a (c + c') ha (by rw [hadd, hc, hc', MonObj.comp_mul])
    have h2 := val _ _ hx hg a c ha hc
    have h3 := val _ _ hx hg' a c' ha hc'
    apply Units.map_injective (f := iK.toMonoidHom) iK.injective
    rw [map_mul, ← h1, ← h2, ← h3, map_add, zpow_add]
  have hL4 := ef_dvd E H D n
  have zeroOf : ∀ a c, ζK ^ D.EF a c = 1 → (n : ℤ) ∣ D.EF a c := fun a c h => (hpK.zpow_eq_one_iff_dvd _).1 h
  have nondegR : ∀ g, g ^ n = 1 → (∀ x, x ^ n = 1 → e x g = 1) → g = 1 := by
    intro g hg h
    obtain ⟨c, hc⟩ := coord g hg
    obtain ⟨c', rfl⟩ := hL4.2 c fun a => by
      obtain ⟨x, hx, hxa⟩ := lift a
      apply zeroOf
      rw [val x g hx hg a _ hxa.symm hc, h x hx, map_one]
    apply inj
    rw [MonObj.comp_one, ← hc]
    exact (hker _).2 ⟨c', rfl⟩
  have nondegL : ∀ x, x ^ n = 1 → (∀ g, g ^ n = 1 → e x g = 1) → x = 1 := by
    intro x hx h
    obtain ⟨a, ha⟩ := coord x hx
    obtain ⟨a', rfl⟩ := hL4.1 a fun c => by
      obtain ⟨g, hg, hgc⟩ := lift c
      apply zeroOf
      rw [val x g hx hg _ c ha hgc.symm, h g hg, map_one]
    apply inj
    rw [MonObj.comp_one, ← ha]
    exact (hker _).2 ⟨a', rfl⟩
  have finK : Finite {y : Over.mk (spMap iK ≫ ξ₀ ≫ f) ⟶ t.G // y ^ n = 1} :=
    tors_finite E H D _ n hn0 ev hadd (fun a => (hker _).2 ⟨a, rfl⟩) (fun y hy => (hon y).1 hy)
  have hfin : Finite {x : Over.mk (ξ₀ ≫ f) ⟶ t.G // x ^ n = 1} :=
    Finite.of_injective (fun x => (⟨extPt _ iK ≫ x.1, tors iK x.1 x.2⟩ :
      {y : Over.mk (spMap iK ≫ ξ₀ ≫ f) ⟶ t.G // y ^ n = 1}))
      (fun x x' h => Subtype.ext (inj _ _ (congrArg Subtype.val h)))
  refine ⟨e, hfin, hl, hr, ?_, nondegR, hweil⟩
  intro χ hχ
  let T : Subgroup (Over.mk (ξ₀ ≫ f) ⟶ t.G) := (powMonoidHom n).ker
  haveI : Finite T := hfin
  let ch : T → (T →* Kˣ) := fun x => MonoidHom.mk' (fun g => Units.map iK.toMonoidHom (e x g)) fun g g' => by
    show Units.map iK.toMonoidHom (e x (g * g')) = _
    rw [hr _ _ _ x.2 g.2 g'.2, map_mul]
  let Φ : T →* (T →* Kˣ) := MonoidHom.mk' ch fun x x' => by
    ext g : 1
    show Units.map iK.toMonoidHom (e ((x : Over.mk (ξ₀ ≫ f) ⟶ t.G) * x') g) =
      Units.map iK.toMonoidHom (e x g) * Units.map iK.toMonoidHom (e x' g)
    rw [← map_mul, hl _ _ _ x.2 x'.2 g.2]
  have hinj : Function.Injective Φ := (injective_iff_map_eq_one Φ).2 fun x hx =>
    Subtype.ext (nondegL x x.2 fun g hg => by
      have h1 : Units.map iK.toMonoidHom (e x g) = 1 := DFunLike.congr_fun hx ⟨g, hg⟩
      exact Units.map_injective (f := iK.toMonoidHom) iK.injective (h1.trans (map_one _).symm))
  haveI : NeZero ((Monoid.exponent T : ℕ) : K) := ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  have hcard := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity T K
  haveI : Finite (T →* Kˣ) := Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
  have hbij := hinj.bijective_of_nat_card_le hcard.le
  obtain ⟨x, hx⟩ := hbij.2 (MonoidHom.mk' (fun g : T => Units.map iK.toMonoidHom (χ g)) fun g g' => by
    show Units.map iK.toMonoidHom (χ ((g : Over.mk (ξ₀ ≫ f) ⟶ t.G) * g')) = _
    rw [hχ _ _ g.2 g'.2, map_mul])
  exact ⟨x, x.2, fun g hg => Units.map_injective (f := iK.toMonoidHom) iK.injective
    (DFunLike.congr_fun hx ⟨g, hg⟩).symm⟩

end GlobalTheory.CompanionTheory.Ar.WeilObj
