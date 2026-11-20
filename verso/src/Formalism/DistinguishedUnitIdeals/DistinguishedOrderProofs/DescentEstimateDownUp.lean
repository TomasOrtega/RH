import Mathlib
import Formalism.DistinguishedUnitIdeals.CoprimeProd
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.GroundTheory
import Formalism.GaussValuationBounds.GaussValueContraction.PhiIterXProof

noncomputable section

namespace Formalism.ExponentWindows

section Coprime

variable {O : Type} [CommRing O]

/- English proof (translation)
Take `⟨N, a, a', h⟩` from `h`. Conclude with `⟨N, a', a, by rw [← h]; ring⟩`.
-/
theorem coprimeRat_symm {ϖ : O} {p q : PowerSeries O} (h : CoprimeRat ϖ p q) :
    CoprimeRat ϖ q p := by
  obtain ⟨N, a, a', h⟩ := h
  exact ⟨N, a', a, by rw [← h]; ring⟩

/- English proof (translation)
Take `⟨N, a, a', h⟩` from `h`. Take `⟨M, b, b', h'⟩` from `h'`. Use `⟨N + M, a * b, a * p * b' + a' * b * p' + a' * b' * q, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add, map_mul, ← h, ← h']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coprimeRat_mul_left {ϖ : O} {p p' q : PowerSeries O} (h : CoprimeRat ϖ p q)
    (h' : CoprimeRat ϖ p' q) : CoprimeRat ϖ (p * p') q := by
  obtain ⟨N, a, a', h⟩ := h
  obtain ⟨M, b, b', h'⟩ := h'
  refine ⟨N + M, a * b, a * p * b' + a' * b * p' + a' * b' * q, ?_⟩
  rw [pow_add, map_mul, ← h, ← h']
  ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, 1, 0, by simp⟩`.
-/
theorem coprimeRat_one_left {ϖ : O} {q : PowerSeries O} : CoprimeRat ϖ 1 q :=
  ⟨0, 1, 0, by simp⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using (coprimeRat_one_left (ϖ := ϖ) (q := q))`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `coprimeRat_mul_left ih h`.
-/
theorem coprimeRat_pow_left {ϖ : O} {p q : PowerSeries O} (h : CoprimeRat ϖ p q) (n : ℕ) :
    CoprimeRat ϖ (p ^ n) q := by
  induction n with
  | zero => simpa using (coprimeRat_one_left (ϖ := ϖ) (q := q))
  | succ n ih => rw [pow_succ]; exact coprimeRat_mul_left ih h

/- English proof (translation)
The claim follows from `coprimeRat_symm (coprimeRat_pow_left (coprimeRat_symm (coprimeRat_pow_left h m)) n)`.
-/
theorem coprimeRat_pow_pow {ϖ : O} {p q : PowerSeries O} (h : CoprimeRat ϖ p q) (m n : ℕ) :
    CoprimeRat ϖ (p ^ m) (q ^ n) :=
  coprimeRat_symm (coprimeRat_pow_left (coprimeRat_symm (coprimeRat_pow_left h m)) n)

/- English proof (translation)
The claim follows from `Finset.prod_induction f (fun x => CoprimeRat ϖ x q) (fun _ _ ha hb => coprimeRat_mul_left ha hb) coprimeRat_one_left h`.
-/
theorem coprimeRat_prod_left {ϖ : O} {ι : Type} (S : Finset ι) (f : ι → PowerSeries O)
    {q : PowerSeries O} (h : ∀ s ∈ S, CoprimeRat ϖ (f s) q) :
    CoprimeRat ϖ (∏ s ∈ S, f s) q :=
  Finset.prod_induction f (fun x => CoprimeRat ϖ x q) (fun _ _ ha hb => coprimeRat_mul_left ha hb)
    coprimeRat_one_left h

end Coprime

section Scalar

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Take `⟨u, E, hu, hE, -, rfl⟩` from `h`. Use `mul_ne_zero hu.ne_zero ?_` and prove the remaining obligations. Rewrite using `[Ne, Polynomial.coe_eq_zero_iff]`. Conclude with `hE.monic.ne_zero`.
-/
theorem unitDist_ne_zero {ϖ : O} {d : ℕ} {p : PowerSeries O} (h : UnitDist ϖ d p) : p ≠ 0 := by
  obtain ⟨u, E, hu, hE, -, rfl⟩ := h
  refine mul_ne_zero hu.ne_zero ?_
  rw [Ne, Polynomial.coe_eq_zero_iff]
  exact hE.monic.ne_zero

/- English proof (translation)
Take `⟨N, a, a', he⟩` from `hc`. Apply `mem_span_pow_of_uniformizer_mul O ϖ hϖ d p hp K N x` to reduce the goal to its premises. Establish `e : PowerSeries.C (ϖ ^ N) * x = a * (x * P) + (a' * x) * p ^ K` using `by rw [← he]; ring`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))`.
-/
theorem mem_of_mul_mem_coprime {ϖ : O} (hϖ : Irreducible ϖ) {d : ℕ} {p P x : PowerSeries O}
    (hp : UnitDist ϖ d p) (K : ℕ) (hc : CoprimeRat ϖ P (p ^ K))
    (h : x * P ∈ Ideal.span {p ^ K}) : x ∈ Ideal.span {p ^ K} := by
  obtain ⟨N, a, a', he⟩ := hc
  apply mem_span_pow_of_uniformizer_mul O ϖ hϖ d p hp K N x
  have e : PowerSeries.C (ϖ ^ N) * x = a * (x * P) + (a' * x) * p ^ K := by rw [← he]; ring
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h)
    (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => intro _ _`. Simplify using the standard rewrite rules. Consider the case `insert t S ht ih`. Introduce `hS hf`.

Establish `hS' : S ⊆ Finset.range ell` using `fun x hx => hS (Finset.mem_insert_of_mem hx)`. Establish `ht' : t < ell` using `Finset.mem_range.mp (hS (Finset.mem_insert_self t S))`. Take `⟨w, rfl⟩` from `Ideal.mem_span_singleton'.mp (ih hS' (fun s hs => hf s (Finset.mem_insert_of_mem hs)))`. Establish `hc : CoprimeRat ϖ (∏ s ∈ S, p s ^ E s) (p t ^ E t)`. Use `coprimeRat_prod_left S _ (fun s hs => ?_)` and prove the remaining obligations.

Establish `hs' : s < ell` using `Finset.mem_range.mp (hS' hs)`. Establish `hne : s ≠ t` using `fun e => ht (e ▸ hs)`. Conclude with `coprimeRat_pow_pow (hP.2 s hs' t ht' hne) _ _`. Establish `hw` using `mem_of_mul_mem_coprime hϖ (hP.1 t ht') (E t) hc (hf t (Finset.mem_insert_self t S))`. Take `⟨m, rfl⟩` from `Ideal.mem_span_singleton'.mp hw`.

Rewrite using `[Finset.prod_insert ht]`. Conclude with `Ideal.mem_span_singleton'.mpr ⟨m, by ring⟩`.
-/
theorem mem_span_prod {ϖ : O} (hϖ : Irreducible ϖ) {ℓ ell : ℕ} {p : ℕ → PowerSeries O}
    (hP : DistinguishedFamily ϖ ℓ ell p) (E : ℕ → ℕ) (f : PowerSeries O) (S : Finset ℕ) :
    S ⊆ Finset.range ell → (∀ s ∈ S, f ∈ Ideal.span {p s ^ E s}) →
      f ∈ Ideal.span {∏ s ∈ S, p s ^ E s} := by
  induction S using Finset.induction_on with
  | empty => intro _ _; simp
  | insert t S ht ih =>
    intro hS hf
    have hS' : S ⊆ Finset.range ell := fun x hx => hS (Finset.mem_insert_of_mem hx)
    have ht' : t < ell := Finset.mem_range.mp (hS (Finset.mem_insert_self t S))
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp
      (ih hS' (fun s hs => hf s (Finset.mem_insert_of_mem hs)))
    have hc : CoprimeRat ϖ (∏ s ∈ S, p s ^ E s) (p t ^ E t) := by
      refine coprimeRat_prod_left S _ (fun s hs => ?_)
      have hs' : s < ell := Finset.mem_range.mp (hS' hs)
      have hne : s ≠ t := fun e => ht (e ▸ hs)
      exact coprimeRat_pow_pow (hP.2 s hs' t ht' hne) _ _
    have hw := mem_of_mul_mem_coprime hϖ (hP.1 t ht') (E t) hc (hf t (Finset.mem_insert_self t S))
    obtain ⟨m, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    rw [Finset.prod_insert ht]
    exact Ideal.mem_span_singleton'.mpr ⟨m, by ring⟩

end Scalar

section Linear

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Establish `hpow : ∀ (n : ℕ) (v : Fin r → O), ϖ ^ n • v ∈ V → v ∈ V`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro v hv`. Simplify using `using hv`.

Consider the case `succ n ih`. Introduce `v hv`. Apply `ih` to reduce the goal to its premises. Apply `hV` to reduce the goal to its premises. Rewrite using `[smul_smul, ← pow_succ']`.

Conclude with `hv`. Establish `: Module.IsTorsionFree O ((Fin r → O) ⧸ V)`. Use `Module.IsTorsionFree.of_smul_eq_zero (fun a q hq => ?_)` and prove the remaining obligations. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective V q`. Distinguish the cases in `ha : a = 0`.

Conclude with `Or.inl ha`. Use `right`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ`. Rewrite `hq` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`.

Apply `hpow n` to reduce the goal to its premises. Use `V.smul_mem (↑u⁻¹ : O) hq` as an intermediate fact. Rewrite `this` using `[smul_smul, ← mul_assoc, Units.inv_mul, one_mul]`. Then use the resulting hypothesis. Take `⟨n, bs⟩` from `Module.basisOfFiniteTypeTorsionFree' (R := O) (M := (Fin r → O) ⧸ V)`. Establish `hdiv : ∀ j, ϖ ^ k ∣ bs.repr (V.mkQ d) j` using `fun j => by`.

Use `h ((bs.coord j).comp V.mkQ) (fun v hv => by` as an intermediate fact. Simplify using `[(Submodule.Quotient.mk_eq_zero V).mpr hv])`. Simplify using `using this`. Use `choose m hm using hdiv`. Take `⟨lam, hlam⟩` from `Submodule.Quotient.mk_surjective V (∑ j, m j • bs j)`.

Use `⟨lam, ?_⟩` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hlam, sub_eq_zero, Finset.smul_sum]`. Establish `hd` using `bs.sum_repr (V.mkQ d)`. Rewrite `hd` using `[Submodule.mkQ_apply]`. Rewrite using `[← hd]`.

Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite `hm` using `[Submodule.mkQ_apply]`. Rewrite using `[hm j, smul_smul]`.
-/
theorem exists_lift_of_dvd {ϖ : O} (hϖ : Irreducible ϖ) {r : ℕ} {V : Submodule O (Fin r → O)}
    (hV : Saturated ϖ V) (d : Fin r → O) (k : ℕ)
    (h : ∀ φ : (Fin r → O) →ₗ[O] O, (∀ v ∈ V, φ v = 0) → ϖ ^ k ∣ φ d) :
    ∃ lam : Fin r → O, d - ϖ ^ k • lam ∈ V := by
  have hpow : ∀ (n : ℕ) (v : Fin r → O), ϖ ^ n • v ∈ V → v ∈ V := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      apply ih
      apply hV
      rw [smul_smul, ← pow_succ']
      exact hv
  have : Module.IsTorsionFree O ((Fin r → O) ⧸ V) := by
    refine Module.IsTorsionFree.of_smul_eq_zero (fun a q hq => ?_)
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective V q
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    apply hpow n
    have := V.smul_mem (↑u⁻¹ : O) hq
    rwa [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
  obtain ⟨n, bs⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := (Fin r → O) ⧸ V)
  have hdiv : ∀ j, ϖ ^ k ∣ bs.repr (V.mkQ d) j := fun j => by
    have := h ((bs.coord j).comp V.mkQ) (fun v hv => by
      simp [(Submodule.Quotient.mk_eq_zero V).mpr hv])
    simpa using this
  choose m hm using hdiv
  obtain ⟨lam, hlam⟩ := Submodule.Quotient.mk_surjective V (∑ j, m j • bs j)
  refine ⟨lam, ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
    hlam, sub_eq_zero, Finset.smul_sum]
  have hd := bs.sum_repr (V.mkQ d)
  rw [Submodule.mkQ_apply] at hd
  rw [← hd]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Submodule.mkQ_apply] at hm
  rw [hm j, smul_smul]

def extF {r : ℕ} (φ : (Fin r → O) →ₗ[O] O) :
    (Fin r → PowerSeries O) →ₗ[PowerSeries O] PowerSeries O :=
  ∑ i, PowerSeries.C (φ (fun j => if i = j then 1 else 0)) • LinearMap.proj i

/- English proof (translation)
Simplify using `[extF]`.
-/
theorem extF_apply {r : ℕ} (φ : (Fin r → O) →ₗ[O] O) (y : Fin r → PowerSeries O) :
    extF φ y = ∑ i, PowerSeries.C (φ (fun j => if i = j then 1 else 0)) * y i := by
  simp [extF]

/- English proof (translation)
Rewrite using `[extF_apply, LinearMap.pi_apply_eq_sum_univ φ v, map_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Simplify using `[cst, smul_eq_mul, mul_comm]`.
-/
theorem extF_cst {r : ℕ} (φ : (Fin r → O) →ₗ[O] O) (v : Fin r → O) :
    extF φ (cst v) = PowerSeries.C (φ v) := by
  rw [extF_apply, LinearMap.pi_apply_eq_sum_univ φ v, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [cst, smul_eq_mul, mul_comm]

/- English proof (translation)
Establish `: ext V ≤ LinearMap.ker (extF φ)` using `Submodule.span_le.mpr (by`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Simplify using `[extF_cst, hφ v hv])`. Conclude with `this hc`.
-/
theorem extF_eq_zero {r : ℕ} (φ : (Fin r → O) →ₗ[O] O) {V : Submodule O (Fin r → O)}
    (hφ : ∀ v ∈ V, φ v = 0) {c : Fin r → PowerSeries O} (hc : c ∈ ext V) : extF φ c = 0 := by
  have : ext V ≤ LinearMap.ker (extF φ) := Submodule.span_le.mpr (by
    rintro _ ⟨v, hv, rfl⟩
    simp [extF_cst, hφ v hv])
  exact this hc

end Linear

/- English proof (translation)
The claim follows from `Submodule.add_mem _ hc (Submodule.smul_mem _ a (Submodule.subset_span ⟨v, hv, rfl⟩))`.
-/
theorem ext_add_const_mem {O : Type} [CommRing O] {r : ℕ} {V : Submodule O (Fin r → O)}
    {c : Fin r → PowerSeries O} (a : PowerSeries O) {v : Fin r → O} (hc : c ∈ ext V)
    (hv : v ∈ V) : c + a • cst v ∈ ext V :=
  Submodule.add_mem _ hc (Submodule.smul_mem _ a (Submodule.subset_span ⟨v, hv, rfl⟩))

section Levels

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Consider the cases of `kk with`. Consider the case `thin`. Take `⟨N, z, hz⟩` from `h`. Conclude with `⟨N + k, z, by rw [pow_add, map_mul, mul_smul]; exact hz⟩`. Consider the case `up`.

Take `⟨N, c, z, hc, hz⟩` from `h`. Conclude with `⟨N + k, c, z, hc, by rw [pow_add, map_mul, mul_smul]; exact hz⟩`. Consider the case `down`. Take `⟨N, c, z, hc, hz⟩` from `h`. Conclude with `⟨N + k, c, z, hc, by rw [pow_add, map_mul, mul_smul]; exact hz⟩`.
-/
theorem levelCond_of_C_smul {ϖ : O} {r : ℕ} {q : PowerSeries O} {H bb : ℕ} {kk : Kind}
    {V : Submodule O (Fin r → O)} {u : Fin r → PowerSeries O} (k : ℕ)
    (h : LevelCond ϖ q H bb kk V (PowerSeries.C (ϖ ^ k) • u)) : LevelCond ϖ q H bb kk V u := by
  cases kk with
  | thin =>
    obtain ⟨N, z, hz⟩ := h
    exact ⟨N + k, z, by rw [pow_add, map_mul, mul_smul]; exact hz⟩
  | up =>
    obtain ⟨N, c, z, hc, hz⟩ := h
    exact ⟨N + k, c, z, hc, by rw [pow_add, map_mul, mul_smul]; exact hz⟩
  | down =>
    obtain ⟨N, c, z, hc, hz⟩ := h
    exact ⟨N + k, c, z, hc, by rw [pow_add, map_mul, mul_smul]; exact hz⟩

/- English proof (translation)
Consider the cases of `kk with`. Consider the case `thin`. Take `⟨N, z, hz⟩` from `h`. Use `⟨N, z + (PowerSeries.C (ϖ ^ N) * R) • cst v, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Use `congrFun hz i` as an intermediate fact. Simplify using `only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this ⊢`. Take the linear combination `this`. Consider the case `up`. Take `⟨N, c, z, hc, hz⟩` from `h`.

Use `⟨N, c, z + (PowerSeries.C (ϖ ^ N) * R) • cst v, hc, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `congrFun hz i` as an intermediate fact. Simplify using `only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this ⊢`. Take the linear combination `this`.

Consider the case `down`. Take `⟨N, c, z, hc, hz⟩` from `h`. Break down `hv with hv | hv | hv` into its components or cases. Conclude with `absurd rfl hv`. Use `⟨N, c + (PowerSeries.C (ϖ ^ N) * R) • cst v, z, ext_add_const_mem _ hc hv, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Use `congrFun hz i` as an intermediate fact. Simplify using `only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this ⊢`. Take the linear combination `this`. Substitute `hv` using the available equality.

Use `⟨N, c, z + (PowerSeries.C (ϖ ^ N) * R) • cst v, hc, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Use `congrFun hz i` as an intermediate fact. Simplify using `only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, add_zero] at this ⊢`. Take the linear combination `this`.
-/
theorem levelCond_add_const {ϖ : O} {r : ℕ} {q R : PowerSeries O} {H bb : ℕ} {kk : Kind}
    {V : Submodule O (Fin r → O)} {u : Fin r → PowerSeries O} (v : Fin r → O)
    (hv : kk ≠ Kind.down ∨ v ∈ V ∨ bb = 0)
    (h : LevelCond ϖ q H bb kk V u) : LevelCond ϖ q H bb kk V (u + (q ^ H * R) • cst v) := by
  cases kk with
  | thin =>
    obtain ⟨N, z, hz⟩ := h
    refine ⟨N, z + (PowerSeries.C (ϖ ^ N) * R) • cst v, ?_⟩
    funext i
    have := congrFun hz i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this ⊢
    linear_combination this
  | up =>
    obtain ⟨N, c, z, hc, hz⟩ := h
    refine ⟨N, c, z + (PowerSeries.C (ϖ ^ N) * R) • cst v, hc, ?_⟩
    funext i
    have := congrFun hz i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this ⊢
    linear_combination this
  | down =>
    obtain ⟨N, c, z, hc, hz⟩ := h
    rcases hv with hv | hv | hv
    · exact absurd rfl hv
    · refine ⟨N, c + (PowerSeries.C (ϖ ^ N) * R) • cst v, z,
        ext_add_const_mem _ hc hv, ?_⟩
      funext i
      have := congrFun hz i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at this ⊢
      linear_combination this
    · subst hv
      refine ⟨N, c, z + (PowerSeries.C (ϖ ^ N) * R) • cst v, hc, ?_⟩
      funext i
      have := congrFun hz i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, add_zero] at this ⊢
      linear_combination this

end Levels

section Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Substitute `hΛ` using the available equality. Consider the cases of `kk with`. Consider the case `thin`. Take `⟨N, z, hz⟩` from `h`. Establish `e` using `congrArg (extF φ) hz`.

Simplify using `only [map_smul, map_sub, extF_cst, smul_eq_mul] at e`. Rewrite using `[if_neg (by decide)]`. Apply `mem_span_pow_of_uniformizer_mul O ϖ hϖ dd q hq _ (N + k)` to reduce the goal to its premises. Rewrite using `[Ideal.mem_span_singleton]`. Conclude with `⟨extF φ z + PowerSeries.C (ϖ ^ N) * R * PowerSeries.C (φ d), by`.

Rewrite using `[pow_add, map_mul]`. Take the linear combination `e⟩`. Consider the case `up`. Take `⟨N, c, z, hc, hz⟩` from `h`. Establish `e` using `congrArg (extF φ) hz`.

Simplify using `only [map_smul, map_sub, map_add, extF_cst, smul_eq_mul] at e`. Rewrite using `[if_pos rfl]`. Establish `hH : q ^ H = q ^ (H - bb) * q ^ bb` using `by rw [← pow_add, Nat.sub_add_cancel (hkb rfl)]`. Apply `mem_span_pow_of_uniformizer_mul O ϖ hϖ dd q hq _ (N + k)` to reduce the goal to its premises. Rewrite using `[Ideal.mem_span_singleton]`.

Conclude with `⟨extF φ c + q ^ bb * (extF φ z + PowerSeries.C (ϖ ^ N) * R * PowerSeries.C (φ d)), by`. Rewrite using `[pow_add, map_mul]`. Take the linear combination `e + (extF φ z + PowerSeries.C (ϖ ^ N) * R * PowerSeries.C (φ d)) * hH⟩`. Consider the case `down`. Take `⟨N, c, z, hc, hz⟩` from `h`.

Establish `e` using `congrArg (extF φ) hz`. Simplify using `only [map_smul, map_sub, map_add, extF_cst, smul_eq_mul] at e`. Rewrite using `[if_neg (by decide)]`. Apply `mem_span_pow_of_uniformizer_mul O ϖ hϖ dd q hq _ (N + k)` to reduce the goal to its premises. Rewrite using `[Ideal.mem_span_singleton]`.

Conclude with `⟨extF φ c + q ^ bb * extF φ z + PowerSeries.C (ϖ ^ N) * R * PowerSeries.C (φ d), by`. Rewrite using `[pow_add, map_mul]`. Take the linear combination `e⟩`.
-/
theorem extF_mem_of_levelCond {ϖ : O} (hϖ : Irreducible ϖ) {r : ℕ} (φ : (Fin r → O) →ₗ[O] O)
    {q Λ R : PowerSeries O} {H bb dd : ℕ} {kk : Kind} {V : Submodule O (Fin r → O)}
    (hq : UnitDist ϖ dd q) (hΛ : Λ = q ^ H * R) (hkb : kk = Kind.up → bb ≤ H)
    {y : Fin r → PowerSeries O} {d : Fin r → O} {k : ℕ}
    (h : LevelCond ϖ q H bb kk V (PowerSeries.C (ϖ ^ k) • y - Λ • cst d)) :
    extF φ y ∈ Ideal.span {q ^ (if kk = Kind.up then H - bb else H)} := by
  subst hΛ
  cases kk with
  | thin =>
    obtain ⟨N, z, hz⟩ := h
    have e := congrArg (extF φ) hz
    simp only [map_smul, map_sub, extF_cst, smul_eq_mul] at e
    rw [if_neg (by decide)]
    apply mem_span_pow_of_uniformizer_mul O ϖ hϖ dd q hq _ (N + k)
    rw [Ideal.mem_span_singleton]
    exact ⟨extF φ z + PowerSeries.C (ϖ ^ N) * R * PowerSeries.C (φ d), by
      rw [pow_add, map_mul]; linear_combination e⟩
  | up =>
    obtain ⟨N, c, z, hc, hz⟩ := h
    have e := congrArg (extF φ) hz
    simp only [map_smul, map_sub, map_add, extF_cst, smul_eq_mul] at e
    rw [if_pos rfl]
    have hH : q ^ H = q ^ (H - bb) * q ^ bb := by rw [← pow_add, Nat.sub_add_cancel (hkb rfl)]
    apply mem_span_pow_of_uniformizer_mul O ϖ hϖ dd q hq _ (N + k)
    rw [Ideal.mem_span_singleton]
    exact ⟨extF φ c + q ^ bb * (extF φ z + PowerSeries.C (ϖ ^ N) * R * PowerSeries.C (φ d)), by
      rw [pow_add, map_mul]
      linear_combination e + (extF φ z + PowerSeries.C (ϖ ^ N) * R * PowerSeries.C (φ d)) * hH⟩
  | down =>
    obtain ⟨N, c, z, hc, hz⟩ := h
    have e := congrArg (extF φ) hz
    simp only [map_smul, map_sub, map_add, extF_cst, smul_eq_mul] at e
    rw [if_neg (by decide)]
    apply mem_span_pow_of_uniformizer_mul O ϖ hϖ dd q hq _ (N + k)
    rw [Ideal.mem_span_singleton]
    exact ⟨extF φ c + q ^ bb * extF φ z + PowerSeries.C (ϖ ^ N) * R * PowerSeries.C (φ d), by
      rw [pow_add, map_mul]; linear_combination e⟩

/- English proof (translation)
Establish `hΛs : ∀ s < ell, abelian₂ p H ell = p s ^ H s * ∏ t ∈ (Finset.range ell).erase s, p t ^ H t` using `fun s hs => (Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs)).symm`. Establish `hmem : ∀ s ∈ Finset.range ell, extF φ y ∈ Ideal.span {p s ^ (fun t => if kind t = Kind.up then H t - b t else H t) s}`. Introduce `s hs`. Take `⟨d', k', h'⟩` from `hII s (Finset.mem_range.1 hs)`. Conclude with `extF_mem_of_levelCond hϖ φ (hP.1 s (Finset.mem_range.1 hs)) (hΛs s (Finset.mem_range.1 hs)) (hup s (Finset.mem_range.1 hs)) h'`.

Take `⟨w, hw⟩` from `Ideal.mem_span_singleton'.mp (mem_span_prod hϖ hP _ (extF φ y) (Finset.range ell) subset_rfl hmem)`. Use `⟨w, ?_⟩` and prove the remaining obligations. Establish `hΛ : abelian₂ p H ell = (∏ s ∈ Finset.range ell, p s ^ (if kind s = Kind.up then H s - b s else H s)) * ∏ s ∈ Finset.range ell, p s ^ (if kind s = Kind.up then b s else 0)`. Unfold `abelian₂`. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl (fun s hs => ?_)` and prove the remaining obligations. Rewrite using `[← pow_add]`. Use `congr 1`. Use `split_ifs with hk`. Use `hup s (Finset.mem_range.1 hs) hk` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Establish `hPE : (∏ s ∈ Finset.range ell, p s ^ (if kind s = Kind.up then H s - b s else H s)) = p s₁ ^ H s₁ * ∏ s ∈ (Finset.range ell).erase s₁, p s ^ (if kind s = Kind.up then H s - b s else H s)`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs₁)]`. Simplify using `[hk₁]`.

Rewrite `h₁` using `[hk₁]`. Take `⟨N, c, z, hc, hz⟩` from `h₁`. Establish `e` using `congrArg (extF φ) hz`. Simplify using `only [map_smul, map_sub, map_add, extF_cst, smul_eq_mul, extF_eq_zero φ hφ hc, mul_zero, zero_add] at e`. Rewrite `e` using `[← hw, hΛ, hPE]`.

Establish `hne : p s₁ ^ H s₁ ≠ 0` using `pow_ne_zero _ (unitDist_ne_zero (hP.1 s₁ hs₁))`. Establish `h2 : (PowerSeries.C (ϖ ^ N) * (PowerSeries.C (ϖ ^ k) * w - (∏ s ∈ Finset.range ell, p s ^ (if kind s = Kind.up then b s else 0)) * PowerSeries.C (φ d))) * (∏ s ∈ (Finset.range ell).erase s₁, p s ^ (if kind s = Kind.up then H s - b s else H s)) = p s₁ ^ b s₁ * extF φ z`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Take the linear combination `e`. Establish `hcop : CoprimeRat ϖ (∏ s ∈ (Finset.range ell).erase s₁, p s ^ (if kind s = Kind.up then H s - b s else H s)) (p s₁ ^ b s₁)`.

Use `coprimeRat_prod_left _ _ (fun s hs => ?_)` and prove the remaining obligations. Conclude with `coprimeRat_pow_pow (hP.2 s (Finset.mem_range.1 (Finset.mem_of_mem_erase hs)) s₁ hs₁ (Finset.ne_of_mem_erase hs)) _ _`. Establish `h3` using `mem_of_mul_mem_coprime hϖ (hP.1 s₁ hs₁) (b s₁) hcop (Ideal.mem_span_singleton'.mpr ⟨extF φ z, by rw [h2, mul_comm]⟩)`. Conclude with `mem_span_pow_of_uniformizer_mul O ϖ hϖ _ _ (hP.1 s₁ hs₁) _ N _ h3`.
-/
theorem down_scalar {ϖ : O} (hϖ : Irreducible ϖ) {ℓ ell r : ℕ} {p : ℕ → PowerSeries O}
    {H b : ℕ → ℕ} {kind : ℕ → Kind} {V : ℕ → Submodule O (Fin r → O)}
    (hP : DistinguishedFamily ϖ ℓ ell p) (hup : ∀ s < ell, kind s = Kind.up → b s ≤ H s)
    {s₁ : ℕ} (hs₁ : s₁ < ell) (hk₁ : kind s₁ = Kind.down) {y : Fin r → PowerSeries O}
    (hII : II ϖ p H b kind V ell y) (φ : (Fin r → O) →ₗ[O] O) (hφ : ∀ v ∈ V s₁, φ v = 0)
    (d : Fin r → O) (k : ℕ)
    (h₁ : LevelCond ϖ (p s₁) (H s₁) (b s₁) (kind s₁) (V s₁)
      (PowerSeries.C (ϖ ^ k) • y - abelian₂ p H ell • cst d)) :
    ∃ w : PowerSeries O, PowerSeries.C (ϖ ^ k) * w -
      (∏ s ∈ Finset.range ell, p s ^ (if kind s = Kind.up then b s else 0)) *
        PowerSeries.C (φ d) ∈ Ideal.span {p s₁ ^ b s₁} := by
  have hΛs : ∀ s < ell, abelian₂ p H ell = p s ^ H s * ∏ t ∈ (Finset.range ell).erase s, p t ^ H t :=
    fun s hs => (Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs)).symm
  have hmem : ∀ s ∈ Finset.range ell, extF φ y ∈
      Ideal.span {p s ^ (fun t => if kind t = Kind.up then H t - b t else H t) s} := by
    intro s hs
    obtain ⟨d', k', h'⟩ := hII s (Finset.mem_range.1 hs)
    exact extF_mem_of_levelCond hϖ φ (hP.1 s (Finset.mem_range.1 hs))
      (hΛs s (Finset.mem_range.1 hs)) (hup s (Finset.mem_range.1 hs)) h'
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp
    (mem_span_prod hϖ hP _ (extF φ y) (Finset.range ell) subset_rfl hmem)
  refine ⟨w, ?_⟩
  have hΛ : abelian₂ p H ell =
      (∏ s ∈ Finset.range ell, p s ^ (if kind s = Kind.up then H s - b s else H s)) *
        ∏ s ∈ Finset.range ell, p s ^ (if kind s = Kind.up then b s else 0) := by
    unfold abelian₂
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun s hs => ?_)
    rw [← pow_add]
    congr 1
    split_ifs with hk
    · have := hup s (Finset.mem_range.1 hs) hk; omega
    · simp
  have hPE : (∏ s ∈ Finset.range ell, p s ^ (if kind s = Kind.up then H s - b s else H s)) =
      p s₁ ^ H s₁ * ∏ s ∈ (Finset.range ell).erase s₁,
        p s ^ (if kind s = Kind.up then H s - b s else H s) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hs₁)]
    simp [hk₁]
  rw [hk₁] at h₁
  obtain ⟨N, c, z, hc, hz⟩ := h₁
  have e := congrArg (extF φ) hz
  simp only [map_smul, map_sub, map_add, extF_cst, smul_eq_mul, extF_eq_zero φ hφ hc, mul_zero,
    zero_add] at e
  rw [← hw, hΛ, hPE] at e
  have hne : p s₁ ^ H s₁ ≠ 0 := pow_ne_zero _ (unitDist_ne_zero (hP.1 s₁ hs₁))
  have h2 : (PowerSeries.C (ϖ ^ N) * (PowerSeries.C (ϖ ^ k) * w -
      (∏ s ∈ Finset.range ell, p s ^ (if kind s = Kind.up then b s else 0)) *
        PowerSeries.C (φ d))) *
      (∏ s ∈ (Finset.range ell).erase s₁, p s ^ (if kind s = Kind.up then H s - b s else H s)) =
      p s₁ ^ b s₁ * extF φ z := by
    apply mul_left_cancel₀ hne
    linear_combination e
  have hcop : CoprimeRat ϖ
      (∏ s ∈ (Finset.range ell).erase s₁, p s ^ (if kind s = Kind.up then H s - b s else H s))
      (p s₁ ^ b s₁) := by
    refine coprimeRat_prod_left _ _ (fun s hs => ?_)
    exact coprimeRat_pow_pow (hP.2 s (Finset.mem_range.1 (Finset.mem_of_mem_erase hs)) s₁ hs₁
      (Finset.ne_of_mem_erase hs)) _ _
  have h3 := mem_of_mul_mem_coprime hϖ (hP.1 s₁ hs₁) (b s₁) hcop
    (Ideal.mem_span_singleton'.mpr ⟨extF φ z, by rw [h2, mul_comm]⟩)
  exact mem_span_pow_of_uniformizer_mul O ϖ hϖ _ _ (hP.1 s₁ hs₁) _ N _ h3

/- English proof (translation)
Take `⟨d, k, h₁⟩` from `hII s₁ hs₁`. Choose the witnesses or unpack the hypotheses as in `⟨lam, hlam⟩ : ∃ lam : Fin r → O, b s₁ = 0 ∨ d - ϖ ^ k • lam ∈ V s₁ := by`. Break down `hlift d k h₁ with h | ⟨lam, h⟩` into its components or cases. Use `exacts [⟨0, Or.inl h⟩, ⟨lam, Or.inr h⟩]`. Use `⟨lam, y - abelian₂ p H ell • cst lam, ?_, by abel⟩` and prove the remaining obligations.

Introduce `s hs`. Establish `key : ∀ (d' : Fin r → O) (k' : ℕ), LevelCond ϖ (p s) (H s) (b s) (kind s) (V s) (PowerSeries.C (ϖ ^ k') • y - abelian₂ p H ell • cst d') → (kind s ≠ Kind.down ∨ d' - ϖ ^ k' • lam ∈ V s ∨ b s = 0) → LevelCond ϖ (p s) (H s) (b s) (kind s) (V s) (y - abelian₂ p H ell • cst lam)`. Introduce `d' k' h' hv`. Apply `levelCond_of_C_smul k'` to reduce the goal to its premises. Establish `e : PowerSeries.C (ϖ ^ k') • (y - abelian₂ p H ell • cst lam) = (PowerSeries.C (ϖ ^ k') • y - abelian₂ p H ell • cst d') + (p s ^ H s * ∏ t ∈ (Finset.range ell).erase s, p t ^ H t) • cst (d' - ϖ ^ k' • lam)`.

Establish `hL` using `Finset.mul_prod_erase (Finset.range ell) (fun t => p t ^ H t) (Finset.mem_range.2 hs)`. Rewrite using `[hL]`. Use function extensionality and compare the values at `i`. Simplify using `[cst, Pi.smul_apply, smul_eq_mul, abelian₂]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `levelCond_add_const _ hv h'`. Distinguish the cases in `hss : s = s₁`. Substitute `hss` using the available equality. Conclude with `key d k h₁ (Or.inr hlam.symm)`.

Take `⟨d', k', h'⟩` from `hII s hs`. Conclude with `key d' k' h' (Or.inl (hnd s hs hss))`.
-/
theorem forward_of_lift {ϖ : O} {ell r : ℕ} {p : ℕ → PowerSeries O}
    {H b : ℕ → ℕ} {kind : ℕ → Kind} {V : ℕ → Submodule O (Fin r → O)}
    {s₁ : ℕ} (hs₁ : s₁ < ell) (hnd : ∀ s < ell, s ≠ s₁ → kind s ≠ Kind.down)
    {y : Fin r → PowerSeries O} (hII : II ϖ p H b kind V ell y)
    (hlift : ∀ (d : Fin r → O) (k : ℕ), LevelCond ϖ (p s₁) (H s₁) (b s₁) (kind s₁) (V s₁)
      (PowerSeries.C (ϖ ^ k) • y - abelian₂ p H ell • cst d) →
        b s₁ = 0 ∨ ∃ lam : Fin r → O, d - ϖ ^ k • lam ∈ V s₁) :
    ∃ (lam : Fin r → O) (ν : Fin r → PowerSeries O), NN ϖ p H b kind V ell ν ∧
      y = abelian₂ p H ell • cst lam + ν := by
  obtain ⟨d, k, h₁⟩ := hII s₁ hs₁
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin r → O, b s₁ = 0 ∨ d - ϖ ^ k • lam ∈ V s₁ := by
    rcases hlift d k h₁ with h | ⟨lam, h⟩
    exacts [⟨0, Or.inl h⟩, ⟨lam, Or.inr h⟩]
  refine ⟨lam, y - abelian₂ p H ell • cst lam, ?_, by abel⟩
  intro s hs
  have key : ∀ (d' : Fin r → O) (k' : ℕ), LevelCond ϖ (p s) (H s) (b s) (kind s) (V s)
      (PowerSeries.C (ϖ ^ k') • y - abelian₂ p H ell • cst d') →
      (kind s ≠ Kind.down ∨ d' - ϖ ^ k' • lam ∈ V s ∨ b s = 0) →
      LevelCond ϖ (p s) (H s) (b s) (kind s) (V s) (y - abelian₂ p H ell • cst lam) := by
    intro d' k' h' hv
    apply levelCond_of_C_smul k'
    have e : PowerSeries.C (ϖ ^ k') • (y - abelian₂ p H ell • cst lam) =
        (PowerSeries.C (ϖ ^ k') • y - abelian₂ p H ell • cst d') +
          (p s ^ H s * ∏ t ∈ (Finset.range ell).erase s, p t ^ H t) • cst (d' - ϖ ^ k' • lam) := by
      have hL := Finset.mul_prod_erase (Finset.range ell) (fun t => p t ^ H t)
        (Finset.mem_range.2 hs)
      rw [hL]
      funext i
      simp [cst, Pi.smul_apply, smul_eq_mul, abelian₂]
      ring
    rw [e]
    exact levelCond_add_const _ hv h'
  by_cases hss : s = s₁
  · subst hss
    exact key d k h₁ (Or.inr hlam.symm)
  · obtain ⟨d', k', h'⟩ := hII s hs
    exact key d' k' h' (Or.inl (hnd s hs hss))

/- English proof (translation)
Introduce `s hs`. Use `⟨lam, 0, ?_⟩` and prove the remaining obligations. Simplify using `using hν s hs`.
-/
theorem II_of_decomp {ϖ : O} {ell r : ℕ} {p : ℕ → PowerSeries O}
    {H b : ℕ → ℕ} {kind : ℕ → Kind} {V : ℕ → Submodule O (Fin r → O)}
    (lam : Fin r → O) (ν : Fin r → PowerSeries O) (hν : NN ϖ p H b kind V ell ν) :
    II ϖ p H b kind V ell (abelian₂ p H ell • cst lam + ν) := by
  intro s hs
  refine ⟨lam, 0, ?_⟩
  simpa using hν s hs

end Model

section Words

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Take `⟨u, E, hu, hE, hdeg, rfl⟩` from `h`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Establish `hmap` using `hE.map_eq_X_pow`. Rewrite `hmap` using `[hdeg]`. Establish `hc : ∀ m, ϖ ∣ PowerSeries.coeff m ((E : PowerSeries O) - PowerSeries.X ^ n)`.

Introduce `m`. Establish `hm : (E - Polynomial.X ^ n).coeff m ∈ Ideal.span {ϖ}`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, Polynomial.map_sub, hmap, Polynomial.map_pow, Polynomial.map_X, sub_self, Polynomial.coeff_zero]`. Rewrite `hm` using `[Ideal.mem_span_singleton]`. Establish `e : ((E : PowerSeries O) - PowerSeries.X ^ n) = ((E - Polynomial.X ^ n : Polynomial O) : PowerSeries O)` using `by push_cast; rfl`.

Rewrite using `[e, Polynomial.coeff_coe]`. Conclude with `hm`. Rewrite using `[Ideal.mem_span_singleton]`. Establish `hd` using `C_dvd_of_forall_dvd_coeff ϖ _ hc`. Establish `e2 : u * (E : PowerSeries O) - u * PowerSeries.X ^ n = u * ((E : PowerSeries O) - PowerSeries.X ^ n)` using `by ring`.

Rewrite using `[e2]`. Conclude with `Dvd.dvd.mul_left hd u`.
-/
theorem sub_unit_X_pow_mem {ϖ : O} {n : ℕ} {p : PowerSeries O} (h : UnitDist ϖ n p) :
    ∃ v : PowerSeries O, IsUnit v ∧ p - v * PowerSeries.X ^ n ∈ Ideal.span {PowerSeries.C ϖ} := by
  obtain ⟨u, E, hu, hE, hdeg, rfl⟩ := h
  refine ⟨u, hu, ?_⟩
  have hmap := hE.map_eq_X_pow
  rw [hdeg] at hmap
  have hc : ∀ m, ϖ ∣ PowerSeries.coeff m ((E : PowerSeries O) - PowerSeries.X ^ n) := by
    intro m
    have hm : (E - Polynomial.X ^ n).coeff m ∈ Ideal.span {ϖ} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.coeff_map, Polynomial.map_sub, hmap,
        Polynomial.map_pow, Polynomial.map_X, sub_self, Polynomial.coeff_zero]
    rw [Ideal.mem_span_singleton] at hm
    have e : ((E : PowerSeries O) - PowerSeries.X ^ n) =
        ((E - Polynomial.X ^ n : Polynomial O) : PowerSeries O) := by
      push_cast; rfl
    rw [e, Polynomial.coeff_coe]
    exact hm
  rw [Ideal.mem_span_singleton]
  have hd := C_dvd_of_forall_dvd_coeff ϖ _ hc
  have e2 : u * (E : PowerSeries O) - u * PowerSeries.X ^ n =
      u * ((E : PowerSeries O) - PowerSeries.X ^ n) := by ring
  rw [e2]
  exact Dvd.dvd.mul_left hd u

/- English proof (translation)
Assume the negation of the conclusion as `hnd`. Establish `hc0 : c ≠ 0` using `by rintro rfl; exact hnd (dvd_zero _)`. Take `⟨e, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ`. Establish `hek : e < k`. Assume the negation of the conclusion as `hle`.

Use `replace hle : k ≤ e := by omega`. Conclude with `hnd ((pow_dvd_pow ϖ hle).mul_left _)`. Take `⟨t, rfl⟩ : ∃ t, k = e + (t + 1)` from `⟨k - e - 1, by omega⟩`. Establish `e1 : PowerSeries.C (ϖ ^ (e + (t + 1))) * w - p₀ ^ b₀ * PowerSeries.C (↑u * ϖ ^ e) = PowerSeries.C (ϖ ^ e) * (PowerSeries.C (ϖ ^ t) * PowerSeries.C ϖ * w - PowerSeries.C (↑u : O) * p₀ ^ b₀)`. Rewrite using `[pow_add, pow_succ, map_mul, map_mul, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hw` using `[e1]`. Establish `h3` using `mem_span_pow_of_uniformizer_mul O ϖ hϖ _ p₁ h₁ b₁ e _ hw`. Take `⟨m, hm⟩` from `Ideal.mem_span_singleton'.mp h3`. Take `⟨v₀, hv₀, hp₀⟩` from `sub_unit_X_pow_mem h₀`.

Take `⟨v₁, hv₁, hp₁⟩` from `sub_unit_X_pow_mem h₁`. Apply `Formalism.NOK.dUDeg_proof O ϖ hϖ.prime ℓ p₀ p₁ v₀ v₁ (PowerSeries.C (↑u : O)) s₀ s₁ b₀ b₁ h01 hb hv₀ hv₁ (u.isUnit.map PowerSeries.C) hp₀ hp₁` to reduce the goal to its premises. Rewrite using `[Ideal.mem_span_pair]`. Conclude with `⟨PowerSeries.C (ϖ ^ t) * w, -m, by linear_combination -hm⟩`.
-/
theorem dvd_of_down_up {ϖ : O} (hϖ : Irreducible ϖ) {ℓ s₀ s₁ b₀ b₁ : ℕ} (h01 : s₀ < s₁)
    (hb : b₀ < ℓ * b₁) {p₀ p₁ : PowerSeries O} (h₀ : UnitDist ϖ (ℓ ^ s₀) p₀)
    (h₁ : UnitDist ϖ (ℓ ^ s₁) p₁) (c : O) (k : ℕ) (w : PowerSeries O)
    (hw : PowerSeries.C (ϖ ^ k) * w - p₀ ^ b₀ * PowerSeries.C c ∈ Ideal.span {p₁ ^ b₁}) :
    ϖ ^ k ∣ c := by
  by_contra hnd
  have hc0 : c ≠ 0 := by rintro rfl; exact hnd (dvd_zero _)
  obtain ⟨e, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
  have hek : e < k := by
    by_contra hle
    replace hle : k ≤ e := by omega
    exact hnd ((pow_dvd_pow ϖ hle).mul_left _)
  obtain ⟨t, rfl⟩ : ∃ t, k = e + (t + 1) := ⟨k - e - 1, by omega⟩
  have e1 : PowerSeries.C (ϖ ^ (e + (t + 1))) * w - p₀ ^ b₀ * PowerSeries.C (↑u * ϖ ^ e) =
      PowerSeries.C (ϖ ^ e) *
        (PowerSeries.C (ϖ ^ t) * PowerSeries.C ϖ * w - PowerSeries.C (↑u : O) * p₀ ^ b₀) := by
    rw [pow_add, pow_succ, map_mul, map_mul, map_mul]; ring
  rw [e1] at hw
  have h3 := mem_span_pow_of_uniformizer_mul O ϖ hϖ _ p₁ h₁ b₁ e _ hw
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp h3
  obtain ⟨v₀, hv₀, hp₀⟩ := sub_unit_X_pow_mem h₀
  obtain ⟨v₁, hv₁, hp₁⟩ := sub_unit_X_pow_mem h₁
  apply Formalism.NOK.dUDeg_proof O ϖ hϖ.prime ℓ p₀ p₁ v₀ v₁ (PowerSeries.C (↑u : O)) s₀ s₁ b₀ b₁
    h01 hb hv₀ hv₁ (u.isUnit.map PowerSeries.C) hp₀ hp₁
  rw [Ideal.mem_span_pair]
  exact ⟨PowerSeries.C (ϖ ^ t) * w, -m, by linear_combination -hm⟩

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ ℓ ell r p H b kind V hℓ hP hV hup s₁ hs₁ hk₁ hthin y`. Prove the components needed by the constructor for the conclusion. Introduce `hII`. Use `forward_of_lift hs₁ (fun s hs hne => by rw [hthin s hs hne]; decide) hII ?_` and prove the remaining obligations. Introduce `d k h₁`.

Distinguish the cases in `hb : b s₁ = 0`. Conclude with `Or.inl hb`. Use `right`. Use `exists_lift_of_dvd hϖ (hV s₁ hs₁) d k (fun φ hφ => ?_)` and prove the remaining obligations. Take `⟨w, hw⟩` from `down_scalar hϖ hP hup hs₁ hk₁ hII φ hφ d k h₁`.

Establish `hB : ∏ s ∈ Finset.range ell, p s ^ (if kind s = Kind.up then b s else 0) = 1`. Use `Finset.prod_eq_one (fun s hs => ?_)` and prove the remaining obligations. Establish `: kind s ≠ Kind.up`. Distinguish the cases in `h : s = s₁`. Substitute `h` using the available equality.

Rewrite using `[hk₁]`. Evaluate the decidable proposition. Rewrite using `[hthin s (Finset.mem_range.1 hs) h]`. Evaluate the decidable proposition. Rewrite using `[if_neg this, pow_zero]`.

Rewrite `hw` using `[hB, one_mul]`. Establish `hw1 : PowerSeries.C (ϖ ^ k) * w - PowerSeries.C (φ d) ∈ Ideal.span {p s₁}` using `Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self _ hb) hw`. Apply `pow_dvd_of_const_mem_span O ϖ hϖ (ℓ ^ s₁) (p s₁) (hP.1 s₁ hs₁) (Nat.one_le_pow _ _ (by omega)) (φ d) k 0 w` to reduce the goal to its premises. Establish `e : PowerSeries.C (ϖ ^ 0) * (PowerSeries.C (φ d) - PowerSeries.C (ϖ ^ k) * w) = -(PowerSeries.C (ϖ ^ k) * w - PowerSeries.C (φ d))` using `by simp`. Rewrite using `[e]`.

Conclude with `Submodule.neg_mem _ hw1`. Introduce and unpack `⟨lam, ν, hν, rfl⟩`. Conclude with `II_of_decomp lam ν hν`.
-/
theorem descent_estimate_down : MD := by
  intro O _ _ _ ϖ hϖ ℓ ell r p H b kind V hℓ hP hV hup s₁ hs₁ hk₁ hthin y
  constructor
  · intro hII
    refine forward_of_lift hs₁ (fun s hs hne => by rw [hthin s hs hne]; decide) hII ?_
    intro d k h₁
    by_cases hb : b s₁ = 0
    · exact Or.inl hb
    right
    refine exists_lift_of_dvd hϖ (hV s₁ hs₁) d k (fun φ hφ => ?_)
    obtain ⟨w, hw⟩ := down_scalar hϖ hP hup hs₁ hk₁ hII φ hφ d k h₁
    have hB : ∏ s ∈ Finset.range ell, p s ^ (if kind s = Kind.up then b s else 0) = 1 := by
      refine Finset.prod_eq_one (fun s hs => ?_)
      have : kind s ≠ Kind.up := by
        by_cases h : s = s₁
        · subst h; rw [hk₁]; decide
        · rw [hthin s (Finset.mem_range.1 hs) h]; decide
      rw [if_neg this, pow_zero]
    rw [hB, one_mul] at hw
    have hw1 : PowerSeries.C (ϖ ^ k) * w - PowerSeries.C (φ d) ∈ Ideal.span {p s₁} :=
      Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self _ hb) hw
    apply pow_dvd_of_const_mem_span O ϖ hϖ (ℓ ^ s₁) (p s₁) (hP.1 s₁ hs₁) (Nat.one_le_pow _ _ (by omega))
      (φ d) k 0 w
    have e : PowerSeries.C (ϖ ^ 0) * (PowerSeries.C (φ d) - PowerSeries.C (ϖ ^ k) * w) =
        -(PowerSeries.C (ϖ ^ k) * w - PowerSeries.C (φ d)) := by simp
    rw [e]
    exact Submodule.neg_mem _ hw1
  · rintro ⟨lam, ν, hν, rfl⟩
    exact II_of_decomp lam ν hν

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ ℓ ell r p H b kind V hℓ hP hV hup s₀ s₁ h01 hs₁ hk₁ hk₀ hthin hb y`. Establish `hs₀ : s₀ < ell` using `by omega`. Prove the components needed by the constructor for the conclusion. Introduce `hII`. Use `forward_of_lift hs₁ (fun s hs hne => ?_) hII ?_` and prove the remaining obligations.

Distinguish the cases in `h0 : s = s₀`. Substitute `h0` using the available equality. Rewrite using `[hk₀]`. Evaluate the decidable proposition. Rewrite using `[hthin s hs h0 hne]`.

Evaluate the decidable proposition. Introduce `d k h₁`. Use `right`. Use `exists_lift_of_dvd hϖ (hV s₁ hs₁) d k (fun φ hφ => ?_)` and prove the remaining obligations. Take `⟨w, hw⟩` from `down_scalar hϖ hP hup hs₁ hk₁ hII φ hφ d k h₁`.

Establish `hB : ∏ s ∈ Finset.range ell, p s ^ (if kind s = Kind.up then b s else 0) = p s₀ ^ b s₀`. Rewrite using `[Finset.prod_eq_single_of_mem s₀ (Finset.mem_range.2 hs₀) (fun s hs hne => ?_)]`. Rewrite using `[if_pos hk₀]`. Establish `: kind s ≠ Kind.up`. Distinguish the cases in `h : s = s₁`.

Substitute `h` using the available equality. Rewrite using `[hk₁]`. Evaluate the decidable proposition. Rewrite using `[hthin s (Finset.mem_range.1 hs) hne h]`. Evaluate the decidable proposition.

Rewrite using `[if_neg this, pow_zero]`. Rewrite `hw` using `[hB]`. Conclude with `dvd_of_down_up hϖ h01 hb (hP.1 s₀ hs₀) (hP.1 s₁ hs₁) (φ d) k w hw`. Introduce and unpack `⟨lam, ν, hν, rfl⟩`. Conclude with `II_of_decomp lam ν hν`.
-/
theorem descent_estimate_down_up : MDU := by
  intro O _ _ _ ϖ hϖ ℓ ell r p H b kind V hℓ hP hV hup s₀ s₁ h01 hs₁ hk₁ hk₀ hthin hb y
  have hs₀ : s₀ < ell := by omega
  constructor
  · intro hII
    refine forward_of_lift hs₁ (fun s hs hne => ?_) hII ?_
    · by_cases h0 : s = s₀
      · subst h0; rw [hk₀]; decide
      · rw [hthin s hs h0 hne]; decide
    intro d k h₁
    right
    refine exists_lift_of_dvd hϖ (hV s₁ hs₁) d k (fun φ hφ => ?_)
    obtain ⟨w, hw⟩ := down_scalar hϖ hP hup hs₁ hk₁ hII φ hφ d k h₁
    have hB : ∏ s ∈ Finset.range ell, p s ^ (if kind s = Kind.up then b s else 0) =
        p s₀ ^ b s₀ := by
      rw [Finset.prod_eq_single_of_mem s₀ (Finset.mem_range.2 hs₀) (fun s hs hne => ?_)]
      · rw [if_pos hk₀]
      · have : kind s ≠ Kind.up := by
          by_cases h : s = s₁
          · subst h; rw [hk₁]; decide
          · rw [hthin s (Finset.mem_range.1 hs) hne h]; decide
        rw [if_neg this, pow_zero]
    rw [hB] at hw
    exact dvd_of_down_up hϖ h01 hb (hP.1 s₀ hs₀) (hP.1 s₁ hs₁) (φ d) k w hw
  · rintro ⟨lam, ν, hν, rfl⟩
    exact II_of_decomp lam ν hν

end Words

end Formalism.ExponentWindows
