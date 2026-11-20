import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.EtaleCohomology.EtaleSheaves.LeafPicCut
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

/- English proof (translation)
Take `⟨s, hs⟩` from `(Algebra.FiniteType.out : (⊤ : Subalgebra k B).FG)`. Use `(Set.Finite.biUnion s.finite_toSet (fun g _ => Place.finite_ord_ne_zero (k := k) (algebraMap B (FractionRing B) g))).subset ?_` and prove the remaining obligations. Introduce `v hv`. Assume the negation of the conclusion as `hcon`. Apply `hv` to reduce the goal to its premises.

Simplify using `only [Set.mem_iUnion, not_exists] at hcon`. Establish `hmem : ∀ g ∈ s, algebraMap B (FractionRing B) g ∈ v.ring`. Introduce `g hg`. Distinguish the cases in `g0 : algebraMap B (FractionRing B) g = 0`. Rewrite using `[g0]`.

Conclude with `zero_mem _`. Establish `h0 : v.ord (algebraMap B (FractionRing B) g) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hcon g hg hne`. Conclude with `(v.ord_nonneg_iff g0).1 h0.ge`.

Introduce `b`. Establish `hb : b ∈ Algebra.adjoin k (s : Set B)` using `hs ▸ Algebra.mem_top`. Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact hmem x hx`. Consider the case `algebraMap r`.

Rewrite using `[← IsScalarTower.algebraMap_apply k B (FractionRing B)]`. Conclude with `v.algebraMap_mem r`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`.

Conclude with `mul_mem hx hy`.
-/
private theorem finite_bad_places (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsFunctionField k (FractionRing B)] :
    {v : Place k (FractionRing B) | ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring}.Finite := by
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k B).FG)
  refine (Set.Finite.biUnion s.finite_toSet (fun g _ =>
    Place.finite_ord_ne_zero (k := k) (algebraMap B (FractionRing B) g))).subset ?_
  intro v hv
  by_contra hcon
  apply hv
  simp only [Set.mem_iUnion, not_exists] at hcon
  have hmem : ∀ g ∈ s, algebraMap B (FractionRing B) g ∈ v.ring := by
    intro g hg
    by_cases g0 : algebraMap B (FractionRing B) g = 0
    · rw [g0]; exact zero_mem _
    · have h0 : v.ord (algebraMap B (FractionRing B) g) = 0 := by
        by_contra hne
        exact hcon g hg hne
      exact (v.ord_nonneg_iff g0).1 h0.ge
  intro b
  have hb : b ∈ Algebra.adjoin k (s : Set B) := hs ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hmem x hx
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply k B (FractionRing B)]
    exact v.algebraMap_mem r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/- English proof (translation)
Establish `hk : ∀ c : k, algebraMap k (FractionRing B) c ∈ (algebraMap B (FractionRing B)).range` using `fun c => ⟨algebraMap k B c, (IsScalarTower.algebraMap_apply k B (FractionRing B) c).symm⟩`. Take `⟨I, hI⟩` from `hf`. Establish `hvP` using `Place.ofHeightOneSpectrum_center B hk v hv`. Establish `hval` using `Place.valuation_ofHeightOneSpectrum B hk (Place.center B v hv)`. Rewrite `hval` using `[hvP]`.

Establish `h1` using `v.valuation_eq_exp_neg_ord f.ne_zero`. Rewrite `h1` using `[hval, GlobalTheory.Idele.valuation_eq_exp_neg_count _ f.ne_zero, WithZero.exp_inj, neg_inj]`. Establish `hspan : FractionalIdeal.spanSingleton (nonZeroDivisors B) (f : FractionRing B) = ((I : FractionalIdeal (nonZeroDivisors B) (FractionRing B))) ^ q`. Use `congrArg (fun J : (FractionalIdeal (nonZeroDivisors B) (FractionRing B))ˣ => (J : FractionalIdeal (nonZeroDivisors B) (FractionRing B))) hI` as an intermediate fact. Simplify using `using this.symm`.

Rewrite `h1` using `[hspan, FractionalIdeal.count_pow]`. Conclude with `⟨_, h1.symm⟩`.
-/
private theorem dvd_ord_of_mem_sel (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
    [IsFunctionField k (FractionRing B)] (q : ℕ) (v : Place k (FractionRing B))
    (hv : ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring) (f : (FractionRing B)ˣ)
    (hf : f ∈ LateralTheory.E.LeafPicCut.sel B q) : (q : ℤ) ∣ v.ord (f : FractionRing B) := by
  have hk : ∀ c : k, algebraMap k (FractionRing B) c ∈ (algebraMap B (FractionRing B)).range :=
    fun c => ⟨algebraMap k B c, (IsScalarTower.algebraMap_apply k B (FractionRing B) c).symm⟩
  obtain ⟨I, hI⟩ := hf
  have hvP := Place.ofHeightOneSpectrum_center B hk v hv
  have hval := Place.valuation_ofHeightOneSpectrum B hk (Place.center B v hv)
  rw [hvP] at hval
  have h1 := v.valuation_eq_exp_neg_ord f.ne_zero
  rw [hval, GlobalTheory.Idele.valuation_eq_exp_neg_count _ f.ne_zero, WithZero.exp_inj, neg_inj] at h1
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors B) (f : FractionRing B) =
      ((I : FractionalIdeal (nonZeroDivisors B) (FractionRing B))) ^ q := by
    have := congrArg (fun J : (FractionalIdeal (nonZeroDivisors B) (FractionRing B))ˣ =>
      (J : FractionalIdeal (nonZeroDivisors B) (FractionRing B))) hI
    simpa using this.symm
  rw [hspan, FractionalIdeal.count_pow] at h1
  exact ⟨_, h1.symm⟩

/- English proof (translation)
Introduce `hS k B _ _ _ _ _ _ q _ hT`. Establish `hfin : Finite (LateralTheory.E.LeafPicCut.selQ B q)`. Establish `: Finite {v : Place k (FractionRing B) | ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring}` using `(finite_bad_places k B).to_subtype`. Set `φ : LateralTheory.E.LeafPicCut.sel B q → ({v : Place k (FractionRing B) | ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} → ZMod q)` to `fun f v => ((v.1.ord ((f.1 : (FractionRing B)ˣ) : FractionRing B) : ℤ) : ZMod q)`. Set `r` to `Function.invFun φ`.

Establish `hall : ∀ f : LateralTheory.E.LeafPicCut.sel B q, (f.1 / (r (φ f)).1 : (FractionRing B)ˣ) ∈ SelAll k (FractionRing B) q`. Introduce `f v`. Establish `hdiv : v.ord (((f.1 / (r (φ f)).1 : (FractionRing B)ˣ)) : FractionRing B) = v.ord (f.1 : FractionRing B) - v.ord ((r (φ f)).1 : FractionRing B)`. Rewrite using `[Units.val_div_eq_div_val, v.ord_div f.1.ne_zero (r (φ f)).1.ne_zero]`. Rewrite using `[hdiv]`.

Distinguish the cases in `hv : ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring`. Conclude with `dvd_sub (dvd_ord_of_mem_sel k B q v hv _ f.2) (dvd_ord_of_mem_sel k B q v hv _ (r (φ f)).2)`. Establish `h` using `congrFun (Function.invFun_eq (f := φ) ⟨f, rfl⟩) ⟨v, hv⟩`. Conclude with `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h`. Take `⟨T, hT⟩` from `hT`.

Use `choose t ht u hu using fun f => hT _ (hall f)`. Use `Finite.of_injective (β := ({v : Place k (FractionRing B) | ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} → ZMod q) × T) (fun x => (φ x.out, ⟨t x.out, ht x.out⟩)) ?_` and prove the remaining obligations. Introduce `x y hxy`. Establish `h1 : φ x.out = φ y.out` using `congrArg Prod.fst hxy`. Establish `h2 : t x.out = t y.out` using `congrArg (fun p => (p.2 : T).1) hxy`.

Establish `hx` using `hu x.out`. Establish `hy` using `hu y.out`. Rewrite `hx`, `hy` using `[div_eq_iff_eq_mul']`. Rewrite using `[← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' y, QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Use `⟨(u x.out)⁻¹ * u y.out, ?_⟩` and prove the remaining obligations.

Simplify using `only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv]`. Rewrite using `[hx, hy, h1, h2, mul_pow, inv_pow]`. Use `group`. Establish `key : Finite {c : ClassGroup B // c ^ q = 1}` using `hS B q hfin`. Conclude with `Finite.of_equiv _ (@Equiv.subtypeEquiv _ _ (fun c : ClassGroup B => c ^ q = 1) (fun c : CommRing.Pic B => c ^ q = 1) (ClassGroup.equivPic B).toEquiv (fun c => by`.

Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_pow, MulEquiv.map_eq_one_iff]))`.
-/
theorem UpperTheory.finite_pic_torsion_of_finite_kummerSelmer :
    LateralTheory.E.LeafPicCut.LeafSelPic → ∀ (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] [IsFunctionField k (FractionRing B)] (q : ℕ) [NeZero q], FinCls q (SelAll k (FractionRing B) q) → Finite {c : CommRing.Pic B // c ^ q = 1} := by
  intro hS k B _ _ _ _ _ _ q _ hT
  have hfin : Finite (LateralTheory.E.LeafPicCut.selQ B q) := by
    have : Finite {v : Place k (FractionRing B) |
        ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} := (finite_bad_places k B).to_subtype
    let φ : LateralTheory.E.LeafPicCut.sel B q →
        ({v : Place k (FractionRing B) | ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} → ZMod q) :=
      fun f v => ((v.1.ord ((f.1 : (FractionRing B)ˣ) : FractionRing B) : ℤ) : ZMod q)
    let r := Function.invFun φ
    have hall : ∀ f : LateralTheory.E.LeafPicCut.sel B q,
        (f.1 / (r (φ f)).1 : (FractionRing B)ˣ) ∈ SelAll k (FractionRing B) q := by
      intro f v
      have hdiv : v.ord (((f.1 / (r (φ f)).1 : (FractionRing B)ˣ)) : FractionRing B) =
          v.ord (f.1 : FractionRing B) - v.ord ((r (φ f)).1 : FractionRing B) := by
        rw [Units.val_div_eq_div_val, v.ord_div f.1.ne_zero (r (φ f)).1.ne_zero]
      rw [hdiv]
      by_cases hv : ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring
      · exact dvd_sub (dvd_ord_of_mem_sel k B q v hv _ f.2) (dvd_ord_of_mem_sel k B q v hv _ (r (φ f)).2)
      · have h := congrFun (Function.invFun_eq (f := φ) ⟨f, rfl⟩) ⟨v, hv⟩
        exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h
    obtain ⟨T, hT⟩ := hT
    choose t ht u hu using fun f => hT _ (hall f)
    refine Finite.of_injective (β := ({v : Place k (FractionRing B) |
        ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} → ZMod q) × T)
      (fun x => (φ x.out, ⟨t x.out, ht x.out⟩)) ?_
    intro x y hxy
    have h1 : φ x.out = φ y.out := congrArg Prod.fst hxy
    have h2 : t x.out = t y.out := congrArg (fun p => (p.2 : T).1) hxy
    have hx := hu x.out
    have hy := hu y.out
    rw [div_eq_iff_eq_mul'] at hx hy
    rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' y, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    refine ⟨(u x.out)⁻¹ * u y.out, ?_⟩
    simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hx, hy, h1, h2, mul_pow, inv_pow]
    group
  have key : Finite {c : ClassGroup B // c ^ q = 1} := hS B q hfin
  exact Finite.of_equiv _ (@Equiv.subtypeEquiv _ _ (fun c : ClassGroup B => c ^ q = 1) (fun c : CommRing.Pic B => c ^ q = 1)
    (ClassGroup.equivPic B).toEquiv (fun c => by
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_pow, MulEquiv.map_eq_one_iff]))
