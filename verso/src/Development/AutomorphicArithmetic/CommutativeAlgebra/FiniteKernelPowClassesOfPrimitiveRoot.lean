import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

/- English proof (translation)
Establish `hsep : (minpoly K c).Separable`. Use `(Polynomial.separable_X_pow_sub_C d hq hd).of_dvd (minpoly.dvd K c ?_)` and prove the remaining obligations. Simplify using `[hc]`. Establish `hsplit : ((minpoly K c).map (algebraMap K (AlgebraicClosure K))).Splits` using `IsAlgClosed.splits _`. Establish `hroot : (minpoly K c).rootSet (AlgebraicClosure K) = {σ₀ c}`.

Rewrite using `[← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly]`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨σ, rfl⟩`. Conclude with `hfix σ`.

Introduce and unpack `rfl`. Conclude with `⟨σ₀, rfl⟩`. Establish `hcard` using `Polynomial.card_rootSet_eq_natDegree hsep hsplit`. Rewrite using `[← minpoly.natDegree_eq_one_iff, ← hcard, Fintype.card_eq_one_iff]`. Use `⟨⟨σ₀ c, by rw [hroot]; rfl⟩, fun y => Subtype.ext ?_⟩` and prove the remaining obligations.

Establish `hy : (y : AlgebraicClosure K) ∈ ({σ₀ c} : Set (AlgebraicClosure K))` using `hroot ▸ y.2`. Conclude with `hy`.
-/
private lemma mem_range_of_fixed {K K' : Type} [Field K] [Field K'] [Algebra K K'] [FiniteDimensional K K']
    (q : ℕ) (hq : (q : K) ≠ 0) (σ₀ : K' →ₐ[K] AlgebraicClosure K) (c : K') (d : K) (hd : d ≠ 0)
    (hc : c ^ q = algebraMap K K' d)
    (hfix : ∀ σ : K' →ₐ[K] AlgebraicClosure K, σ c = σ₀ c) : c ∈ (algebraMap K K').range := by
  have hsep : (minpoly K c).Separable := by
    refine (Polynomial.separable_X_pow_sub_C d hq hd).of_dvd (minpoly.dvd K c ?_)
    simp [hc]
  have hsplit : ((minpoly K c).map (algebraMap K (AlgebraicClosure K))).Splits := IsAlgClosed.splits _
  have hroot : (minpoly K c).rootSet (AlgebraicClosure K) = {σ₀ c} := by
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly]
    ext y
    constructor
    · rintro ⟨σ, rfl⟩
      exact hfix σ
    · rintro rfl
      exact ⟨σ₀, rfl⟩
  have hcard := Polynomial.card_rootSet_eq_natDegree hsep hsplit
  rw [← minpoly.natDegree_eq_one_iff, ← hcard, Fintype.card_eq_one_iff]
  refine ⟨⟨σ₀ c, by rw [hroot]; rfl⟩, fun y => Subtype.ext ?_⟩
  have hy : (y : AlgebraicClosure K) ∈ ({σ₀ c} : Set (AlgebraicClosure K)) := hroot ▸ y.2
  exact hy

/- English proof (translation)
Introduce `K K' _ _ _ _ q _ ⟨ζ, hζ⟩`. Use `haveI := hζ.neZero'`. Establish `hq : ((q : ℕ) : K) ≠ 0` using `NeZero.ne _`. Establish `hq0 : q ≠ 0` using `NeZero.ne q`. Set `σ₀ : K' →ₐ[K] AlgebraicClosure K` to `IsAlgClosed.lift`.

Set `S : Set Kˣ` to `{a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q}`. Set `bb : Kˣ → K'` to `fun a => if h : ∃ b : K', algebraMap K K' (a : K) = b ^ q then h.choose else 1`. Establish `hbb : ∀ a ∈ S, algebraMap K K' (a : K) = bb a ^ q`. Introduce `a ha`. Establish `ha' : ∃ b : K', algebraMap K K' (a : K) = b ^ q` using `ha`.

Simplify using `only [bb, dif_pos ha']`. Conclude with `ha'.choose_spec`. Establish `hbb0 : ∀ a ∈ S, bb a ≠ 0`. Introduce `a ha h0`. Establish `h` using `hbb a ha`.

Rewrite `h` using `[h0, zero_pow hq0]`. Conclude with `a.ne_zero ((algebraMap K K').injective (by rw [h, map_zero]))`. Set `sig : Kˣ → (K' →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K` to `fun a σ => σ (bb a) / σ₀ (bb a)`. Establish `hsig : ∀ a ∈ S, ∀ σ, sig a σ ∈ Polynomial.nthRootsFinset q (1 : AlgebraicClosure K)`. Introduce `a ha σ`.

Rewrite using `[Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hq0)]`. Establish `h1 : σ (bb a) ^ q = σ₀ (bb a) ^ q`. Rewrite using `[← map_pow, ← map_pow, ← hbb a ha, AlgHom.commutes, AlgHom.commutes]`. Establish `h2 : σ₀ (bb a) ≠ 0` using `(map_ne_zero σ₀).mpr (hbb0 a ha)`. Simplify using `only [sig, div_pow, h1, div_self (pow_ne_zero _ h2)]`.

Establish `hfin : (sig '' S).Finite`. Use `(Set.Finite.pi (t := fun _ => (Polynomial.nthRootsFinset q (1 : AlgebraicClosure K) : Set _)) (fun _ => Finset.finite_toSet _)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `Set.mem_univ_pi.mpr (fun σ => hsig a ha σ)`. Set `rep : ((K' →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K) → Kˣ` to `fun f => if h : ∃ a ∈ S, sig a = f then h.choose else 1`.

Use `⟨hfin.toFinset.image rep, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Establish `hex : ∃ a' ∈ S, sig a' = sig a` using `⟨a, ha, rfl⟩`. Establish `htS : rep (sig a) ∈ S ∧ sig (rep (sig a)) = sig a`. Simplify using `only [rep, dif_pos hex]`.

Conclude with `hex.choose_spec`. Use `⟨rep (sig a), Finset.mem_image.mpr ⟨sig a, hfin.mem_toFinset.mpr ⟨a, ha, rfl⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Use `set t := rep (sig a) with ht`. Establish `hat` using `hbb0 a ha`. Establish `htt` using `hbb0 t htS.1`.

Set `c : K'` to `bb a / bb t`. Establish `hc : c ^ q = algebraMap K K' ((a : K) / (t : K))`. Rewrite using `[map_div₀, hbb a ha, hbb t htS.1, div_pow]`. Establish `hd : (a : K) / (t : K) ≠ 0` using `div_ne_zero a.ne_zero t.ne_zero`. Establish `hfix : ∀ σ : K' →ₐ[K] AlgebraicClosure K, σ c = σ₀ c`.

Introduce `σ`. Establish `e` using `congrFun htS.2 σ`. Simplify using `only [sig] at e`. Establish `h1 : σ (bb t) ≠ 0` using `(map_ne_zero σ).mpr htt`. Establish `h2 : σ₀ (bb t) ≠ 0` using `(map_ne_zero σ₀).mpr htt`.

Establish `h3 : σ₀ (bb a) ≠ 0` using `(map_ne_zero σ₀).mpr hat`. Simplify using `only [c, map_div₀]`. Rewrite using `[div_eq_div_iff h1 h2]`. Rewrite `e` using `[div_eq_div_iff h2 h3]`. Take the linear combination `-e`.

Take `⟨e, he⟩` from `mem_range_of_fixed q hq σ₀ c _ hd hc hfix`. Establish `he0 : e ≠ 0`. Introduce and unpack `rfl`. Rewrite `he` using `[map_zero]`. Conclude with `div_ne_zero hat htt he.symm`.

Use `⟨Units.mk0 e he0, ?_⟩` and prove the remaining obligations. Use `ext`. Apply `(algebraMap K K').injective` to reduce the goal to its premises. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_pow, he, hc, map_div₀]`. Establish `: algebraMap K K' (t : K) ≠ 0` using `(map_ne_zero _).mpr t.ne_zero`.

Clear the denominators using the available nonvanishing facts.
-/
theorem UpperTheory.finite_kernel_powClasses_of_primitive_root :
    ∀ (K K' : Type) [Field K] [Field K'] [Algebra K K'] [FiniteDimensional K K'] (q : ℕ) [NeZero q], (∃ ζ : K, IsPrimitiveRoot ζ q) → FinCls q {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q} := by
  intro K K' _ _ _ _ q _ ⟨ζ, hζ⟩
  classical
  haveI := hζ.neZero'
  have hq : ((q : ℕ) : K) ≠ 0 := NeZero.ne _
  have hq0 : q ≠ 0 := NeZero.ne q
  let σ₀ : K' →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let S : Set Kˣ := {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q}
  let bb : Kˣ → K' := fun a => if h : ∃ b : K', algebraMap K K' (a : K) = b ^ q then h.choose else 1
  have hbb : ∀ a ∈ S, algebraMap K K' (a : K) = bb a ^ q := by
    intro a ha
    have ha' : ∃ b : K', algebraMap K K' (a : K) = b ^ q := ha
    simp only [bb, dif_pos ha']
    exact ha'.choose_spec
  have hbb0 : ∀ a ∈ S, bb a ≠ 0 := by
    intro a ha h0
    have h := hbb a ha
    rw [h0, zero_pow hq0] at h
    exact a.ne_zero ((algebraMap K K').injective (by rw [h, map_zero]))
  let sig : Kˣ → (K' →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K := fun a σ => σ (bb a) / σ₀ (bb a)
  have hsig : ∀ a ∈ S, ∀ σ, sig a σ ∈ Polynomial.nthRootsFinset q (1 : AlgebraicClosure K) := by
    intro a ha σ
    rw [Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hq0)]
    have h1 : σ (bb a) ^ q = σ₀ (bb a) ^ q := by
      rw [← map_pow, ← map_pow, ← hbb a ha, AlgHom.commutes, AlgHom.commutes]
    have h2 : σ₀ (bb a) ≠ 0 := (map_ne_zero σ₀).mpr (hbb0 a ha)
    simp only [sig, div_pow, h1, div_self (pow_ne_zero _ h2)]
  have hfin : (sig '' S).Finite := by
    refine (Set.Finite.pi (t := fun _ => (Polynomial.nthRootsFinset q (1 : AlgebraicClosure K) : Set _))
      (fun _ => Finset.finite_toSet _)).subset ?_
    rintro _ ⟨a, ha, rfl⟩
    exact Set.mem_univ_pi.mpr (fun σ => hsig a ha σ)
  let rep : ((K' →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K) → Kˣ :=
    fun f => if h : ∃ a ∈ S, sig a = f then h.choose else 1
  refine ⟨hfin.toFinset.image rep, ?_⟩
  intro a ha
  have hex : ∃ a' ∈ S, sig a' = sig a := ⟨a, ha, rfl⟩
  have htS : rep (sig a) ∈ S ∧ sig (rep (sig a)) = sig a := by
    simp only [rep, dif_pos hex]
    exact hex.choose_spec
  refine ⟨rep (sig a), Finset.mem_image.mpr ⟨sig a, hfin.mem_toFinset.mpr ⟨a, ha, rfl⟩, rfl⟩, ?_⟩
  set t := rep (sig a) with ht
  have hat := hbb0 a ha
  have htt := hbb0 t htS.1
  let c : K' := bb a / bb t
  have hc : c ^ q = algebraMap K K' ((a : K) / (t : K)) := by
    rw [map_div₀, hbb a ha, hbb t htS.1, div_pow]
  have hd : (a : K) / (t : K) ≠ 0 := div_ne_zero a.ne_zero t.ne_zero
  have hfix : ∀ σ : K' →ₐ[K] AlgebraicClosure K, σ c = σ₀ c := by
    intro σ
    have e := congrFun htS.2 σ
    simp only [sig] at e
    have h1 : σ (bb t) ≠ 0 := (map_ne_zero σ).mpr htt
    have h2 : σ₀ (bb t) ≠ 0 := (map_ne_zero σ₀).mpr htt
    have h3 : σ₀ (bb a) ≠ 0 := (map_ne_zero σ₀).mpr hat
    simp only [c, map_div₀]
    rw [div_eq_div_iff h1 h2]
    rw [div_eq_div_iff h2 h3] at e
    linear_combination -e
  obtain ⟨e, he⟩ := mem_range_of_fixed q hq σ₀ c _ hd hc hfix
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [map_zero] at he
    exact div_ne_zero hat htt he.symm
  refine ⟨Units.mk0 e he0, ?_⟩
  ext
  apply (algebraMap K K').injective
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_pow, he, hc, map_div₀]
  have : algebraMap K K' (t : K) ≠ 0 := (map_ne_zero _).mpr t.ne_zero
  field_simp
