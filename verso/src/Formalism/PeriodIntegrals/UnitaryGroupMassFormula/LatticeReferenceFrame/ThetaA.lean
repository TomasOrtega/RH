import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Development

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.TH

variable (I : Formalism.MainNotions.S.AutInst)

def sg : 𝓞 I.E →+* 𝓞 I.E := NumberField.RingOfIntegers.mapRingHom (starRingEnd I.E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sg_coe (x : 𝓞 I.E) : ((sg I x : 𝓞 I.E) : I.E) = star (x : I.E) := rfl

/- English proof (translation)
Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[sg_coe, sg_coe, star_star]`.
-/
theorem sg_sg (x : 𝓞 I.E) : sg I (sg I x) = x := by
  apply NumberField.RingOfIntegers.ext
  rw [sg_coe, sg_coe, star_star]

/- English proof (translation)
Use `show algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) c) = _`. Rewrite using `[← IsScalarTower.algebraMap_apply (𝓞 I.F) (𝓞 I.E) I.E, IsScalarTower.algebraMap_apply (𝓞 I.F) I.F I.E]`.
-/
theorem coe_alg (c : 𝓞 I.F) :
    ((algebraMap (𝓞 I.F) (𝓞 I.E) c : 𝓞 I.E) : I.E) = algebraMap I.F I.E (c : I.F) := by
  show algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) c) = _
  rw [← IsScalarTower.algebraMap_apply (𝓞 I.F) (𝓞 I.E) I.E,
    IsScalarTower.algebraMap_apply (𝓞 I.F) I.F I.E]

/- English proof (translation)
Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[sg_coe]`. Establish `h : ((algebraMap (𝓞 I.F) (𝓞 I.E) c : 𝓞 I.E) : I.E) = algebraMap I.F I.E (c : I.F)` using `by show algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) c) = _`. Rewrite using `[← IsScalarTower.algebraMap_apply (𝓞 I.F) (𝓞 I.E) I.E, IsScalarTower.algebraMap_apply (𝓞 I.F) I.F I.E]`. Rewrite using `[h]`.

Conclude with `(I.cm.fixed _).2 ⟨_, rfl⟩`.
-/
theorem sg_alg (c : 𝓞 I.F) : sg I (algebraMap (𝓞 I.F) (𝓞 I.E) c) = algebraMap (𝓞 I.F) (𝓞 I.E) c := by
  apply NumberField.RingOfIntegers.ext
  rw [sg_coe]
  have h : ((algebraMap (𝓞 I.F) (𝓞 I.E) c : 𝓞 I.E) : I.E) = algebraMap I.F I.E (c : I.F) := by
    show algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) c) = _
    rw [← IsScalarTower.algebraMap_apply (𝓞 I.F) (𝓞 I.E) I.E,
      IsScalarTower.algebraMap_apply (𝓞 I.F) I.F I.E]
  rw [h]
  exact (I.cm.fixed _).2 ⟨_, rfl⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `(I.cm.fixed (y : I.E)).1 hy`. Establish `hi : IsIntegral ℤ (algebraMap I.F I.E a)`. Rewrite using `[ha]`. Conclude with `y.isIntegral_coe`. Establish `hi' : IsIntegral ℤ a` using `(isIntegral_algebraMap_iff (algebraMap I.F I.E).injective).mp hi`.

Set `c : 𝓞 I.F` to `⟨a, (mem_integralClosure_iff _ _).mpr hi'⟩`. Use `⟨c, ?_⟩` and prove the remaining obligations. Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[coe_alg]`. Conclude with `ha`.
-/
theorem fixed_int (y : 𝓞 I.E) (hy : star (y : I.E) = y) :
    ∃ c : 𝓞 I.F, algebraMap (𝓞 I.F) (𝓞 I.E) c = y := by
  obtain ⟨a, ha⟩ := (I.cm.fixed (y : I.E)).1 hy
  have hi : IsIntegral ℤ (algebraMap I.F I.E a) := by
    rw [ha]; exact y.isIntegral_coe
  have hi' : IsIntegral ℤ a := (isIntegral_algebraMap_iff (algebraMap I.F I.E).injective).mp hi
  let c : 𝓞 I.F := ⟨a, (mem_integralClosure_iff _ _).mpr hi'⟩
  refine ⟨c, ?_⟩
  apply NumberField.RingOfIntegers.ext
  rw [coe_alg]
  exact ha

def cj (P : HeightOneSpectrum (𝓞 I.E)) : HeightOneSpectrum (𝓞 I.E) where
  asIdeal := P.asIdeal.comap (sg I)
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro h
    have : sg I x ∈ P.asIdeal.comap (sg I) := by
      rw [Ideal.mem_comap, sg_sg]; exact hx
    rw [h, Ideal.mem_bot] at this
    apply hx0
    rw [← sg_sg I x, this, map_zero]

/- English proof (translation)
The claim follows from `Ideal.mem_comap`.
-/
theorem mem_cj (P : HeightOneSpectrum (𝓞 I.E)) (x : 𝓞 I.E) : x ∈ (cj I P).asIdeal ↔ sg I x ∈ P.asIdeal :=
  Ideal.mem_comap

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[mem_cj, mem_cj, sg_sg]`.
-/
theorem cj_cj (P : HeightOneSpectrum (𝓞 I.E)) : cj I (cj I P) = P := by
  ext x
  rw [mem_cj, mem_cj, sg_sg]

/- English proof (translation)
Use extensionality with `c`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, mem_cj, sg_alg]`.
-/
theorem comap_cj (P : HeightOneSpectrum (𝓞 I.E)) :
    (cj I P).asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) := by
  ext c
  rw [Ideal.mem_comap, Ideal.mem_comap, mem_cj, sg_alg]

/- English proof (translation)
Introduce `hfix`. Establish `hg0 : (g : 𝓞 I.F) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Establish `hgv : (g : 𝓞 I.F) ∈ P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E))`. Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `hP`.

Set `v : HeightOneSpectrum (𝓞 I.F)` to `{ asIdeal := P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) isPrime := Ideal.IsPrime.comap _ ne_bot := fun h => hg0 (by rw [h, Ideal.mem_bot] at hgv; exact hgv) }`. Establish `hcard` using `hS v hgv`. Set `P' : {w : HeightOneSpectrum (𝓞 I.E) // w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal}` to `⟨P, rfl⟩`. Take `⟨x, hx, hxu⟩` from `(Nat.card_eq_two_iff' P').mp hcard`. Set `cx : {w : HeightOneSpectrum (𝓞 I.E) // w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal}` to `⟨cj I x.1, by rw [comap_cj]; exact x.2⟩`.

Establish `hcx : cx ≠ P'`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : cj I x.1 = P` using `congrArg Subtype.val h`.

Rewrite using `[← cj_cj I x.1, h1, hfix]`. Establish `hcxx : cj I x.1 = x.1` using `congrArg Subtype.val (hxu cx hcx)`. Establish `hne : P.asIdeal ≠ x.1.asIdeal`. Introduce `h`. Apply `hx` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(HeightOneSpectrum.ext h).symm`. Establish `hnle : ¬ P.asIdeal ≤ x.1.asIdeal` using `fun h => hne (P.isMaximal.eq_of_le x.1.isPrime.ne_top h)`. Take `⟨θ, hθP, hθx⟩` from `SetLike.not_le_iff_exists.mp hnle`. Establish `hfixy : star ((θ * sg I θ : 𝓞 I.E) : I.E) = ((θ * sg I θ : 𝓞 I.E) : I.E)` using `by show star ((θ : I.E) * (sg I θ : I.E)) = (θ : I.E) * (sg I θ : I.E)`.

Rewrite using `[sg_coe, star_mul, star_star, mul_comm]`. Take `⟨c, hc⟩` from `fixed_int I _ hfixy`. Establish `hyP : θ * sg I θ ∈ P.asIdeal` using `Ideal.mul_mem_right _ _ hθP`. Establish `hcv : c ∈ x.1.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E))`. Rewrite using `[x.2]`.

Use `show c ∈ P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E))`. Rewrite using `[Ideal.mem_comap, hc]`. Conclude with `hyP`. Rewrite `hcv` using `[Ideal.mem_comap, hc]`. Break down `x.1.isPrime.mem_or_mem hcv with h | h` into its components or cases.

Conclude with `hθx h`. Apply `hθx` to reduce the goal to its premises. Establish `: θ ∈ (cj I x.1).asIdeal` using `by rw [mem_cj]; exact h`. Rewrite `this` using `[hcxx]`. Then use the resulting hypothesis.
-/
theorem cj_ne (g : ℕ) (hg : 1 ≤ g) (hS : PI.ScRefExists.Sk.SplitG I g) (P : HeightOneSpectrum (𝓞 I.E))
    (hP : (g : 𝓞 I.E) ∈ P.asIdeal) : cj I P ≠ P := by
  intro hfix
  have hg0 : (g : 𝓞 I.F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hgv : (g : 𝓞 I.F) ∈ P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) := by
    rw [Ideal.mem_comap, map_natCast]; exact hP
  let v : HeightOneSpectrum (𝓞 I.F) :=
    { asIdeal := P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E))
      isPrime := Ideal.IsPrime.comap _
      ne_bot := fun h => hg0 (by rw [h, Ideal.mem_bot] at hgv; exact hgv) }
  have hcard := hS v hgv
  let P' : {w : HeightOneSpectrum (𝓞 I.E) //
      w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} := ⟨P, rfl⟩
  obtain ⟨x, hx, hxu⟩ := (Nat.card_eq_two_iff' P').mp hcard
  let cx : {w : HeightOneSpectrum (𝓞 I.E) //
      w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} := ⟨cj I x.1, by rw [comap_cj]; exact x.2⟩
  have hcx : cx ≠ P' := by
    intro h
    apply hx
    apply Subtype.ext
    have h1 : cj I x.1 = P := congrArg Subtype.val h
    rw [← cj_cj I x.1, h1, hfix]
  have hcxx : cj I x.1 = x.1 := congrArg Subtype.val (hxu cx hcx)
  have hne : P.asIdeal ≠ x.1.asIdeal := by
    intro h
    apply hx
    apply Subtype.ext
    exact (HeightOneSpectrum.ext h).symm
  have hnle : ¬ P.asIdeal ≤ x.1.asIdeal := fun h =>
    hne (P.isMaximal.eq_of_le x.1.isPrime.ne_top h)
  obtain ⟨θ, hθP, hθx⟩ := SetLike.not_le_iff_exists.mp hnle
  have hfixy : star ((θ * sg I θ : 𝓞 I.E) : I.E) = ((θ * sg I θ : 𝓞 I.E) : I.E) := by
    show star ((θ : I.E) * (sg I θ : I.E)) = (θ : I.E) * (sg I θ : I.E)
    rw [sg_coe, star_mul, star_star, mul_comm]
  obtain ⟨c, hc⟩ := fixed_int I _ hfixy
  have hyP : θ * sg I θ ∈ P.asIdeal := Ideal.mul_mem_right _ _ hθP
  have hcv : c ∈ x.1.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) := by
    rw [x.2]
    show c ∈ P.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E))
    rw [Ideal.mem_comap, hc]; exact hyP
  rw [Ideal.mem_comap, hc] at hcv
  rcases x.1.isPrime.mem_or_mem hcv with h | h
  · exact hθx h
  · apply hθx
    have : θ ∈ (cj I x.1).asIdeal := by rw [mem_cj]; exact h
    rwa [hcxx] at this

/- English proof (translation)
Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Conclude with `⟨a, by push_cast; ring⟩`.
-/
theorem ge_of_mem (g : ℕ) (y : 𝓞 I.E) (hy : y ∈ Ideal.span {(g : 𝓞 I.E)}) :
    PI.ScRefExists.Sk.GE I g (y : I.E) := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  exact ⟨a, by push_cast; ring⟩

end PI.ScRefExists.TH
