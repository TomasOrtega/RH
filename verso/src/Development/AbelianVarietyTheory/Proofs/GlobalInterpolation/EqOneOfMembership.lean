import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.TrivialColumnStabiliser

noncomputable section

namespace GlobalTheory.Proof.EqOneOfMembership

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser
open scoped TensorProduct

section Local

variable {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ}

/- English proof (translation)
Use `set π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) with hπ`. Establish `hM' : π.mapMatrix M = 1` using `hM`. Establish `h1 : (∑ i ∈ Finset.range m, M ^ i) * (M - 1) = 0`. Rewrite using `[geom_sum_mul, hpow, sub_self]`. Establish `h2 : π.mapMatrix (∑ i ∈ Finset.range m, M ^ i) = (m : Matrix (Fin n) (Fin n) _)`.

Rewrite using `[map_sum]`. Simplify using `only [map_pow, hM', one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`. Establish `h3 : IsUnit (π (∑ i ∈ Finset.range m, M ^ i).det)`. Rewrite using `[RingHom.map_det, h2, ← Matrix.isUnit_iff_isUnit_det]`. Use `(hm.map π).map (algebraMap _ (Matrix (Fin n) (Fin n) (O ⧸ IsLocalRing.maximalIdeal O)))` as an intermediate fact.

Simplify using `using this`. Establish `h4 : IsUnit (∑ i ∈ Finset.range m, M ^ i).det`. Assume the negation of the conclusion as `h`. Establish `: π (∑ i ∈ Finset.range m, M ^ i).det = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 ((IsLocalRing.mem_maximalIdeal _).2 h)`. Rewrite `h3` using `[this]`.

Conclude with `not_isUnit_zero h3`. Establish `h5` using `(Matrix.isUnit_iff_isUnit_det _).2 h4`. Conclude with `sub_eq_zero.1 (h5.mul_right_eq_zero.1 h1)`.
-/
theorem eq_one_of_red_eq_one {M : Matrix (Fin n) (Fin n) O}
    (hM : M.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) = 1) {m : ℕ}
    (hm : IsUnit (m : O)) (hpow : M ^ m = 1) : M = 1 := by
  set π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) with hπ
  have hM' : π.mapMatrix M = 1 := hM
  have h1 : (∑ i ∈ Finset.range m, M ^ i) * (M - 1) = 0 := by
    rw [geom_sum_mul, hpow, sub_self]
  have h2 : π.mapMatrix (∑ i ∈ Finset.range m, M ^ i) = (m : Matrix (Fin n) (Fin n) _) := by
    rw [map_sum]
    simp only [map_pow, hM', one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have h3 : IsUnit (π (∑ i ∈ Finset.range m, M ^ i).det) := by
    rw [RingHom.map_det, h2, ← Matrix.isUnit_iff_isUnit_det]
    have := (hm.map π).map (algebraMap _ (Matrix (Fin n) (Fin n) (O ⧸ IsLocalRing.maximalIdeal O)))
    simpa using this
  have h4 : IsUnit (∑ i ∈ Finset.range m, M ^ i).det := by
    by_contra h
    have : π (∑ i ∈ Finset.range m, M ^ i).det = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [this] at h3
    exact not_isUnit_zero h3
  have h5 := (Matrix.isUnit_iff_isUnit_det _).2 h4
  exact sub_eq_zero.1 (h5.mul_right_eq_zero.1 h1)

/- English proof (translation)
Establish `e2` using `(Commute.one_right (a - 1)).add_pow_prime_pow_eq hg r`. Establish `hle : r ≤ g ^ r` using `(Nat.lt_pow_self hg.one_lt).le`. Rewrite `e2` using `[sub_add_cancel, h0, pow_eq_zero_of_le hle ha]`. Simplify using `using e2`.
-/
theorem pow_prime_pow_eq_one {A : Type} [Ring A] {g r : ℕ} (hg : g.Prime) (h0 : (g : A) = 0)
    {a : A} (ha : (a - 1) ^ r = 0) : a ^ g ^ r = 1 := by
  have e2 := (Commute.one_right (a - 1)).add_pow_prime_pow_eq hg r
  have hle : r ≤ g ^ r := (Nat.lt_pow_self hg.one_lt).le
  rw [sub_add_cancel, h0, pow_eq_zero_of_le hle ha] at e2
  simpa using e2

/- English proof (translation)
Take `⟨r, hr⟩` from `hM`. Use `set π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) with hπ`. Establish `h0 : (g : Matrix (Fin n) (Fin n) (O ⧸ IsLocalRing.maximalIdeal O)) = 0`. Establish `: (g : O ⧸ IsLocalRing.maximalIdeal O) = 0`. Rewrite using `[← map_natCast π]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 hgm`. Rewrite using `[← map_natCast (algebraMap (O ⧸ IsLocalRing.maximalIdeal O) _), this, map_zero]`. Establish `h1 : (π.mapMatrix M) ^ g ^ r = 1` using `pow_prime_pow_eq_one hg h0 hr`. Take `⟨e, m, hm, hord⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (n := orderOf M) hfin.orderOf_pos.ne' g hg.ne_one`. Use `⟨r + e, eq_one_of_red_eq_one (m := m) ?_ ?_ ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `π.mapMatrix _ = 1`. Rewrite using `[map_pow, pow_add, pow_mul, h1, one_pow]`. Establish `hc : IsCoprime (m : O) (g : O)`. Use `Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hg).mpr hm).symm` as an intermediate fact. Simplify using `using this.map (Int.castRingHom O)`.

Assume the negation of the conclusion as `h`. Take `⟨u, v, huv⟩` from `hc`. Establish `: (1 : O) ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[← huv]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 h)) (Ideal.mul_mem_left _ _ hgm)`.

Conclude with `(IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)`. Rewrite using `[← pow_mul, pow_add, mul_assoc, ← hord, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]`.
-/
theorem exists_pow_eq_one {g : ℕ} (hg : g.Prime) (hgm : (g : O) ∈ IsLocalRing.maximalIdeal O)
    {M : Matrix (Fin n) (Fin n) O}
    (hM : IsNilpotent (M.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) - 1))
    (hfin : IsOfFinOrder M) : ∃ a : ℕ, M ^ g ^ a = 1 := by
  obtain ⟨r, hr⟩ := hM
  set π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) with hπ
  have h0 : (g : Matrix (Fin n) (Fin n) (O ⧸ IsLocalRing.maximalIdeal O)) = 0 := by
    have : (g : O ⧸ IsLocalRing.maximalIdeal O) = 0 := by
      rw [← map_natCast π]; exact Ideal.Quotient.eq_zero_iff_mem.2 hgm
    rw [← map_natCast (algebraMap (O ⧸ IsLocalRing.maximalIdeal O) _), this, map_zero]
  have h1 : (π.mapMatrix M) ^ g ^ r = 1 := pow_prime_pow_eq_one hg h0 hr
  obtain ⟨e, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (n := orderOf M) hfin.orderOf_pos.ne' g hg.ne_one
  refine ⟨r + e, eq_one_of_red_eq_one (m := m) ?_ ?_ ?_⟩
  · change π.mapMatrix _ = 1
    rw [map_pow, pow_add, pow_mul, h1, one_pow]
  · have hc : IsCoprime (m : O) (g : O) := by
      have := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hg).mpr hm).symm
      simpa using this.map (Int.castRingHom O)
    by_contra h
    obtain ⟨u, v, huv⟩ := hc
    have : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [← huv]
      exact add_mem (Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 h))
        (Ideal.mul_mem_left _ _ hgm)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)
  · rw [← pow_mul, pow_add, mul_assoc, ← hord, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]

end Local

/- English proof (translation)
Establish `key : ∀ y : GL (Fin k) A, y ∈ upperUni k A ↔ (y : Matrix (Fin k) (Fin k) A).BlockTriangular id ∧ ∀ i, (y : Matrix (Fin k) (Fin k) A) i i = 1` using `fun y => ⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2⟩, fun h i j => ⟨fun hij => h.1 hij, h.2 i⟩⟩`. Establish `diag : ∀ a b : Matrix (Fin k) (Fin k) A, a.BlockTriangular id → b.BlockTriangular id → ∀ i, (a * b) i i = a i i * b i i`. Introduce `a b ha hb i`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)` and prove the remaining obligations.

Break down `lt_or_gt_of_ne hj with h | h` into its components or cases. Rewrite using `[ha (show id j < id i from h), zero_mul]`. Rewrite using `[hb (show id i < id j from h), mul_zero]`. Establish `hx' : x ∈ upperUni k A`. Proceed by induction on `hx using Subgroup.closure_induction with`.

Consider the case `mem y hy => exact hy`. Consider the case `one => exact (key _).2 ⟨Matrix.blockTriangular_one, fun i => by simp⟩`. Consider the case `mul a b _ _ ha hb`. Rewrite `ha`, `hb`, the goal using `[key]`. Conclude with `⟨ha.1.mul hb.1, fun i => by rw [Units.val_mul, diag _ _ ha.1 hb.1, ha.2, hb.2, one_mul]⟩`.

Consider the case `inv a _ ha`. Rewrite `ha`, the goal using `[key]`. Set `_` to `a.invertible`. Establish `h1 : ((a⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).BlockTriangular id`. Rewrite using `[Matrix.coe_units_inv]`.

Conclude with `Matrix.blockTriangular_inv_of_blockTriangular ha.1`. Use `⟨h1, fun i => ?_⟩` and prove the remaining obligations. Use `diag _ _ h1 ha.1 i` as an intermediate fact. Rewrite `this` using `[Units.inv_mul, ha.2, mul_one, Matrix.one_apply_eq]`. Conclude with `this.symm`.

Rewrite `hx'` using `[key]`. Use `set h := (x : Matrix (Fin k) (Fin k) A)`. Establish `h1 : h.charpoly = ∏ i : Fin k, (Polynomial.X - Polynomial.C (h i i))` using `Matrix.charpoly_of_isUpperTriangular h hx'.1`. Establish `h2` using `Matrix.aeval_self_charpoly h`. Rewrite `h2` using `[h1]`.

Conclude with `⟨k, by simpa [hx'.2, Finset.prod_const] using h2⟩`.
-/
theorem isNilpotent_of_mem_closure {A : Type} [CommRing A] {k : ℕ} {x : GL (Fin k) A}
    (hx : x ∈ Subgroup.closure (upperUni k A)) :
    IsNilpotent ((x : Matrix (Fin k) (Fin k) A) - 1) := by
  have key : ∀ y : GL (Fin k) A, y ∈ upperUni k A ↔
      (y : Matrix (Fin k) (Fin k) A).BlockTriangular id ∧
        ∀ i, (y : Matrix (Fin k) (Fin k) A) i i = 1 := fun y =>
    ⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2⟩,
      fun h i j => ⟨fun hij => h.1 hij, h.2 i⟩⟩
  have diag : ∀ a b : Matrix (Fin k) (Fin k) A, a.BlockTriangular id → b.BlockTriangular id →
      ∀ i, (a * b) i i = a i i * b i i := by
    intro a b ha hb i
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
    rcases lt_or_gt_of_ne hj with h | h
    · rw [ha (show id j < id i from h), zero_mul]
    · rw [hb (show id i < id j from h), mul_zero]
  have hx' : x ∈ upperUni k A := by
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hy
    | one => exact (key _).2 ⟨Matrix.blockTriangular_one, fun i => by simp⟩
    | mul a b _ _ ha hb =>
      rw [key] at ha hb ⊢
      exact ⟨ha.1.mul hb.1, fun i => by rw [Units.val_mul, diag _ _ ha.1 hb.1, ha.2, hb.2, one_mul]⟩
    | inv a _ ha =>
      rw [key] at ha ⊢
      let _ := a.invertible
      have h1 : ((a⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).BlockTriangular id := by
        rw [Matrix.coe_units_inv]
        exact Matrix.blockTriangular_inv_of_blockTriangular ha.1
      refine ⟨h1, fun i => ?_⟩
      have := diag _ _ h1 ha.1 i
      rw [Units.inv_mul, ha.2, mul_one, Matrix.one_apply_eq] at this
      exact this.symm
  rw [key] at hx'
  set h := (x : Matrix (Fin k) (Fin k) A)
  have h1 : h.charpoly = ∏ i : Fin k, (Polynomial.X - Polynomial.C (h i i)) :=
    Matrix.charpoly_of_isUpperTriangular h hx'.1
  have h2 := Matrix.aeval_self_charpoly h
  rw [h1] at h2
  exact ⟨k, by simpa [hx'.2, Finset.prod_const] using h2⟩

/- English proof (translation)
Introduce `a b h`. Use `Units.ext (Matrix.ext fun i j => hφ ?_)` and prove the remaining obligations. Conclude with `congrArg (fun g : GL (Fin k) B => g.val i j) h`.
-/
theorem bc_injective {A B : Type} [CommRing A] [CommRing B] {k : ℕ} {φ : A →+* B}
    (hφ : Function.Injective φ) : Function.Injective (bc (n := Fin k) φ) := by
  intro a b h
  refine Units.ext (Matrix.ext fun i j => hφ ?_)
  exact congrArg (fun g : GL (Fin k) B => g.val i j) h

/- English proof (translation)
The claim follows from `Units.ext (Matrix.ext fun _ _ => rfl)`.
-/
theorem bc_bc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {k : ℕ} (φ : A →+* B)
    (ψ : B →+* C) (x : GL (Fin k) A) : bc ψ (bc φ x) = bc (ψ.comp φ) x :=
  Units.ext (Matrix.ext fun _ _ => rfl)

/- English proof (translation)
Take `⟨z, hz, rfl⟩` from `hx`. Establish `hinj : Function.Injective (bc (n` using `Fin k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) := bc_injective Subtype.val_injective`. Establish `hz' : IsOfFinOrder z` using `(hinj.isOfFinOrder_iff).1 hfin`. Establish `hgm : (g : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]`.

Establish `e : (((g : v.adicCompletionIntegers F)) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (g : 𝓞 F))`. Rewrite using `[map_natCast, map_natCast]`. Both sides reduce to the same expression. Rewrite using `[e, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `((v.valuation_lt_one_iff_mem _).2 hv).ne`.

Take `⟨a, ha⟩` from `exists_pow_eq_one hg hgm (M := z.val) (isNilpotent_of_mem_closure hz) (Units.isOfFinOrder_val.2 hz')`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, show z ^ g ^ a = 1 from Units.ext (by simpa using ha), map_one]`.
-/
theorem iwU_pow_eq_one {F : Type} [Field F] [NumberField F] {k g : ℕ} (hg : g.Prime)
    {v : HeightOneSpectrum (𝓞 F)} (hv : (g : 𝓞 F) ∈ v.asIdeal)
    {x : GL (Fin k) (v.adicCompletion F)} (hx : x ∈ iwU F k v) (hfin : IsOfFinOrder x) :
    ∃ a : ℕ, x ^ g ^ a = 1 := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hinj : Function.Injective
      (bc (n := Fin k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) :=
    bc_injective Subtype.val_injective
  have hz' : IsOfFinOrder z := (hinj.isOfFinOrder_iff).1 hfin
  have hgm : (g : v.adicCompletionIntegers F) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have e : (((g : v.adicCompletionIntegers F)) : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (g : 𝓞 F)) := by
      rw [map_natCast, map_natCast]; rfl
    rw [e, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ((v.valuation_lt_one_iff_mem _).2 hv).ne
  obtain ⟨a, ha⟩ := exists_pow_eq_one hg hgm (M := z.val) (isNilpotent_of_mem_closure hz)
    (Units.isOfFinOrder_val.2 hz')
  refine ⟨a, ?_⟩
  rw [← map_pow, show z ^ g ^ a = 1 from Units.ext (by simpa using ha), map_one]

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => intro x hx`. Simplify using `using hx`. Consider the case `succ a ih`. Introduce `x hx`.

Apply `ih` to reduce the goal to its premises. Assume the negation of the conclusion as `hne`. Use `Formalism.LogVandermondeBounds.StandardLattice.primeOrderFinrank E k g (x ^ g ^ a).val hg (by rw [← Units.val_pow_eq_pow_val, ← pow_mul, ← pow_succ, hx, Units.val_one]) (fun h => hne (Units.ext h))` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_one_of_pow_prime_pow {E : Type} [Field E] [NumberField E] {k g : ℕ} (hg : g.Prime)
    (hbig : Module.finrank ℚ E * k < g - 1) (a : ℕ) :
    ∀ x : GL (Fin k) E, x ^ g ^ a = 1 → x = 1 := by
  induction a with
  | zero => intro x hx; simpa using hx
  | succ a ih =>
    intro x hx
    apply ih
    by_contra hne
    have := Formalism.LogVandermondeBounds.StandardLattice.primeOrderFinrank E k g (x ^ g ^ a).val hg
      (by rw [← Units.val_pow_eq_pow_val, ← pow_mul, ← pow_succ, hx, Units.val_one])
      (fun h => hne (Units.ext h))
    omega

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

/- English proof (translation)
Take `⟨c, hc⟩` from `L.y_bij.2 (Quotient.mk'' ⟨y, hy⟩)`. Take `⟨a, ha, b, hb, hab⟩` from `(DoubleCoset.eq _ _ _ _).1 hc`. Establish `hab' : y = a.1 * (L.y c).1 * b.1` using `congrArg Subtype.val hab`. Establish `ha' : a.1 ∈ ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)` using `ha`. Establish `hb' : b.1 ∈ L.U` using `hb`.

Establish `h2 : a.1⁻¹ * γ * a.1 ∈ L.U.map (MulAut.conj (L.y c).1).toMonoidHom`. Use `⟨_, mul_mem (mul_mem hb' hγ2) (inv_mem hb'), ?_⟩` and prove the remaining obligations. Rewrite using `[hab', MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Use `group`. Take `⟨δ, hδ, hδe⟩` from `mul_mem (mul_mem (inv_mem ha') hγ1) ha'`.

Rewrite `h2` using `[← hδe]`. Take `⟨s, hs⟩` from `(L.stabI_range c δ hδ).2 h2`. Establish `h4 : IsOfFinOrder δ`. Use `(Subgroup.subtype _).isOfFinOrder ((L.stabI c).isOfFinOrder (isOfFinOrder_of_finite s))` as an intermediate fact. Rewrite `this` using `[hs]`.

Conclude with `this`. Establish `h5` using `(MulAut.conj a.1).toMonoidHom.isOfFinOrder ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).isOfFinOrder h4)`. Rewrite `h5` using `[hδe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Use `h5 using 1` and compare the differences between its conclusion and the goal. Use `group`.
-/
theorem isOfFinOrder_of_mem (L : ColLevel R F E sp gp C A clsLat)
    {y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (hy : y ∈ UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))
    {γ : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (hγ1 : γ ∈ ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))
    (hγ2 : y⁻¹ * γ * y ∈ L.U) : IsOfFinOrder γ := by
  obtain ⟨c, hc⟩ := L.y_bij.2 (Quotient.mk'' ⟨y, hy⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := (DoubleCoset.eq _ _ _ _).1 hc
  have hab' : y = a.1 * (L.y c).1 * b.1 := congrArg Subtype.val hab
  have ha' : a.1 ∈ ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) := ha
  have hb' : b.1 ∈ L.U := hb
  have h2 : a.1⁻¹ * γ * a.1 ∈ L.U.map (MulAut.conj (L.y c).1).toMonoidHom := by
    refine ⟨_, mul_mem (mul_mem hb' hγ2) (inv_mem hb'), ?_⟩
    rw [hab', MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  obtain ⟨δ, hδ, hδe⟩ := mul_mem (mul_mem (inv_mem ha') hγ1) ha'
  rw [← hδe] at h2
  obtain ⟨s, hs⟩ := (L.stabI_range c δ hδ).2 h2
  have h4 : IsOfFinOrder δ := by
    have := (Subgroup.subtype _).isOfFinOrder ((L.stabI c).isOfFinOrder
      (isOfFinOrder_of_finite s))
    rw [hs] at this
    exact this
  have h5 := (MulAut.conj a.1).toMonoidHom.isOfFinOrder
    ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).isOfFinOrder h4)
  rw [hδe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h5
  convert h5 using 1
  group

/- English proof (translation)
Establish `hfin` using `isOfFinOrder_of_mem L hy hγ1 hU`. Take `⟨δ, hδ, rfl⟩` from `hγ1`. Establish `hloc` using `((L.U_eq _).1 hU).2 v`. Establish `hiw` using `(L.Uloc_g i v hv _ (L.Uloc_le v hloc)).1 hloc`. Rewrite `hiw` using `[bc_bc]`.

Generalize the expression as in `((RingHom.fst _ _).comp (L.splitG i v hv).toRingHom).comp (prV (E := E) v) = ψ at hiw`. Generalize the expression as in `L.frG i v hv = w at hiw`. Rewrite `hiw` using `[map_mul, map_mul, map_inv, bc_bc]`. Establish `hfin1` using `(bc ψ).isOfFinOrder hfin`. Rewrite `hfin1` using `[bc_bc]`.

Generalize the expression as in `ψ.comp (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) = j at hiw hfin1`. Generalize the expression as in `bc ψ y = t at hiw`. Set `Φ : GL (Fin R.k) E →* GL (Fin R.k) (v.adicCompletion F)` to `(MulAut.conj (t * w)⁻¹).toMonoidHom.comp (bc j)`. Establish `hΦinj : Function.Injective Φ` using `(MulAut.conj (t * w)⁻¹).injective.comp (bc_injective j.injective)`. Establish `hmem : Φ δ ∈ iwU F R.k v`.

Use `hiw using 1` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `(t * w)⁻¹ * bc j δ * (t * w)⁻¹⁻¹ = _`. Use `group`. Establish `hfin' : IsOfFinOrder (Φ δ)` using `(MulAut.conj (t * w)⁻¹).toMonoidHom.isOfFinOrder hfin1`. Take `⟨a, ha⟩` from `iwU_pow_eq_one hg hv hmem hfin'`.

Establish `h1 : δ ^ gp i ^ a = 1` using `hΦinj (by rw [map_pow, ha, map_one])`. Rewrite using `[eq_one_of_pow_prime_pow hg hi a δ h1, map_one]`.
-/
theorem eq_one_of_mem (L : ColLevel R F E sp gp C A clsLat) (i : Fin 2) (hg : (gp i).Prime)
    (hi : Module.finrank ℚ E * R.k < gp i - 1)
    {v : HeightOneSpectrum (𝓞 F)} (hv : (gp i : 𝓞 F) ∈ v.asIdeal)
    {y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (hy : y ∈ UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))
    {γ : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (hγ1 : γ ∈ ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))
    (hU : y⁻¹ * γ * y ∈ L.U) : γ = 1 := by
  have hfin := isOfFinOrder_of_mem L hy hγ1 hU
  obtain ⟨δ, hδ, rfl⟩ := hγ1
  have hloc := ((L.U_eq _).1 hU).2 v
  have hiw := (L.Uloc_g i v hv _ (L.Uloc_le v hloc)).1 hloc
  rw [bc_bc] at hiw
  generalize ((RingHom.fst _ _).comp (L.splitG i v hv).toRingHom).comp
    (prV (E := E) v) = ψ at hiw
  generalize L.frG i v hv = w at hiw
  rw [map_mul, map_mul, map_inv, bc_bc] at hiw
  have hfin1 := (bc ψ).isOfFinOrder hfin
  rw [bc_bc] at hfin1
  generalize ψ.comp (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) = j at hiw hfin1
  generalize bc ψ y = t at hiw
  let Φ : GL (Fin R.k) E →* GL (Fin R.k) (v.adicCompletion F) :=
    (MulAut.conj (t * w)⁻¹).toMonoidHom.comp (bc j)
  have hΦinj : Function.Injective Φ :=
    (MulAut.conj (t * w)⁻¹).injective.comp (bc_injective j.injective)
  have hmem : Φ δ ∈ iwU F R.k v := by
    convert hiw using 1
    change (t * w)⁻¹ * bc j δ * (t * w)⁻¹⁻¹ = _
    group
  have hfin' : IsOfFinOrder (Φ δ) := (MulAut.conj (t * w)⁻¹).toMonoidHom.isOfFinOrder hfin1
  obtain ⟨a, ha⟩ := iwU_pow_eq_one hg hv hmem hfin'
  have h1 : δ ^ gp i ^ a = 1 := hΦinj (by rw [map_pow, ha, map_one])
  rw [eq_one_of_pow_prime_pow hg hi a δ h1, map_one]

end Level

/- English proof (translation)
Introduce `D Lv u hbig hs y hy`. Set `_` to `D.host.cmStar`. Take `⟨i, hi⟩` from `hbig`. Establish `hf : D.R.f ≠ 0` using `by unfold Ranks.f Ranks.n; positivity`. Take `⟨v, hv⟩` from `(Nat.card_ne_zero.1 ((hs i).1.trans_ne hf)).1`.

Rewrite using `[eq_bot_iff]`. Introduce `γ hγ`. Rewrite `hγ` using `[mem_stabGroup]`. Conclude with `Subgroup.mem_bot.2 (eq_one_of_mem (Lv u) i (D.host.g_prime i) (by rw [finrank_host D]; exact hi) hv hy hγ.1 hγ.2)`.
-/
theorem columnStabilisersTrivial : ColumnStabilisersTrivial := by
  intro D Lv u hbig hs y hy
  let _ := D.host.cmStar
  obtain ⟨i, hi⟩ := hbig
  have hf : D.R.f ≠ 0 := by unfold Ranks.f Ranks.n; positivity
  obtain ⟨v, hv⟩ := (Nat.card_ne_zero.1 ((hs i).1.trans_ne hf)).1
  rw [eq_bot_iff]
  intro γ hγ
  rw [mem_stabGroup] at hγ
  exact Subgroup.mem_bot.2 (eq_one_of_mem (Lv u) i (D.host.g_prime i)
    (by rw [finrank_host D]; exact hi) hv hy hγ.1 hγ.2)

end GlobalTheory.Proof.EqOneOfMembership

end
