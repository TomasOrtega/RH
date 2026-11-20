import Mathlib
open NumberField Polynomial

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Establish `hmem : a ∈ RingHom.ker ρ` using `ha`. Establish `hn : ((Ideal.absNorm (RingHom.ker ρ) : ℕ) : 𝓞 F) ∈ RingHom.ker ρ` using `Ideal.absNorm_mem _`. Rewrite `hn` using `[RingHom.mem_ker, map_natCast]`.

Take `⟨χ, hχ⟩` from `exists_ne (0 : X)`. Establish `h1 : (Ideal.absNorm (RingHom.ker ρ) : ℕ) • χ = 0`. Use `congrArg (fun f : Module.End ℤ X => f χ) hn` as an intermediate fact. Simplify using `using this`. Rewrite `h1` using `[← Nat.cast_smul_eq_nsmul ℤ]`.

Establish `h2 : Ideal.absNorm (RingHom.ker ρ) = 0`. Break down `smul_eq_zero.mp h1 with h | h` into its components or cases. Conclude with `h` after adjusting the coercions. Conclude with `absurd h hχ`. Rewrite `h2` using `[Ideal.absNorm_eq_zero_iff]`.

Rewrite `hmem` using `[h2]`. Simplify using `using hmem`.
-/
theorem ringOfIntegers_action_injective (F : Type) [Field F] [NumberField F] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Nontrivial X] (ρ : 𝓞 F →+* Module.End ℤ X) :
    Function.Injective ρ := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hmem : a ∈ RingHom.ker ρ := ha
  have hn : ((Ideal.absNorm (RingHom.ker ρ) : ℕ) : 𝓞 F) ∈ RingHom.ker ρ := Ideal.absNorm_mem _
  rw [RingHom.mem_ker, map_natCast] at hn
  obtain ⟨χ, hχ⟩ := exists_ne (0 : X)
  have h1 : (Ideal.absNorm (RingHom.ker ρ) : ℕ) • χ = 0 := by
    have := congrArg (fun f : Module.End ℤ X => f χ) hn
    simpa using this
  rw [← Nat.cast_smul_eq_nsmul ℤ] at h1
  have h2 : Ideal.absNorm (RingHom.ker ρ) = 0 := by
    rcases smul_eq_zero.mp h1 with h | h
    · exact_mod_cast h
    · exact absurd h hχ
  rw [Ideal.absNorm_eq_zero_iff] at h2
  rw [h2] at hmem
  simpa using hmem

/- English proof (translation)
Use `set B := Module.Free.chooseBasis ℤ X`. Set `T : Module.End ℤ X` to `B.constr ℤ (fun s => ∑ r, ((B.repr (ρ a (B s)) r) / p) • B r)`. Establish `hT : algebraMap ℤ (Module.End ℤ X) p * T = ρ a`. Apply `B.ext` to reduce the goal to its premises. Introduce `s`.

Rewrite using `[Module.End.mul_apply, Module.algebraMap_end_apply]`. Simplify using `only [T, Module.Basis.constr_basis, Finset.smul_sum, smul_smul]`. Use `conv_rhs => rw [← B.sum_repr (ρ a (B s))]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[Int.mul_ediv_cancel' (h _ r)]`.

Take `⟨f, hfm, hf⟩` from `Algebra.IsIntegral.isIntegral (R := ℤ) T`. Establish `hf' : aeval T f = 0` using `by rw [aeval_def]; exact hf`. Establish `h1` using `Polynomial.scaleRoots_aeval_eq_zero (r := p) hf'`. Rewrite `h1` using `[hT]`. Establish `h2 : aeval a (f.scaleRoots p) = 0`.

Apply `ringOfIntegers_action_injective F X ρ` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use `Polynomial.aeval_algHom_apply (ρ.toIntAlgHom) a (f.scaleRoots p)` as an intermediate fact. Express the relevant statement in the definitionally equal form `ρ.toIntAlgHom _ = 0`. Rewrite using `[← this]`.

Conclude with `h1`. Establish `h3 : aeval (algebraMap (𝓞 F) F a) (f.scaleRoots p) = 0`. Rewrite using `[Polynomial.aeval_algebraMap_apply, h2, map_zero]`. Establish `hpF : (algebraMap ℤ F p) ≠ 0` using `by simpa using hp`. Use `set β : F := algebraMap (𝓞 F) F a / algebraMap ℤ F p with hβdef`.

Establish `hβa : algebraMap ℤ F p * β = algebraMap (𝓞 F) F a`. Rewrite using `[hβdef]`. Clear the denominators using the available nonvanishing facts. Establish `h4 : eval₂ (algebraMap ℤ F) β f = 0`. Establish `e` using `Polynomial.scaleRoots_eval₂_mul (p := f) (algebraMap ℤ F) β p`.

Rewrite `e` using `[hβa, ← aeval_def, h3]`. Conclude with `(mul_eq_zero.mp e.symm).resolve_left (pow_ne_zero _ hpF)`. Establish `hβ : IsIntegral ℤ β` using `⟨f, hfm, h4⟩`. Set `y : 𝓞 F` to `⟨β, hβ⟩`. Establish `hy : p • y = a`.

Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Rewrite using `[map_zsmul, zsmul_eq_mul]`. Establish `: algebraMap (𝓞 F) F y = β` using `rfl`. Rewrite using `[this, ← hβa]`. Simplify using the standard rewrite rules.

Introduce `i`. Use `⟨b.repr y i, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, map_zsmul, Finsupp.smul_apply, smul_eq_mul]`.
-/
theorem dvd_coord_of_action_dvd (F : Type) [Field F] [NumberField F] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Nontrivial X]
    (ρ : 𝓞 F →+* Module.End ℤ X) (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F))
    (p : ℤ) (hp : p ≠ 0) (a : 𝓞 F)
    (h : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
      p ∣ (Module.Free.chooseBasis ℤ X).repr (ρ a χ) r) :
    ∀ i, p ∣ b.repr a i := by
  set B := Module.Free.chooseBasis ℤ X
  let T : Module.End ℤ X := B.constr ℤ (fun s => ∑ r, ((B.repr (ρ a (B s)) r) / p) • B r)
  have hT : algebraMap ℤ (Module.End ℤ X) p * T = ρ a := by
    apply B.ext
    intro s
    rw [Module.End.mul_apply, Module.algebraMap_end_apply]
    simp only [T, Module.Basis.constr_basis, Finset.smul_sum, smul_smul]
    conv_rhs => rw [← B.sum_repr (ρ a (B s))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Int.mul_ediv_cancel' (h _ r)]
  obtain ⟨f, hfm, hf⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) T
  have hf' : aeval T f = 0 := by rw [aeval_def]; exact hf
  have h1 := Polynomial.scaleRoots_aeval_eq_zero (r := p) hf'
  rw [hT] at h1
  have h2 : aeval a (f.scaleRoots p) = 0 := by
    apply ringOfIntegers_action_injective F X ρ
    rw [map_zero]
    have := Polynomial.aeval_algHom_apply (ρ.toIntAlgHom) a (f.scaleRoots p)
    change ρ.toIntAlgHom _ = 0
    rw [← this]
    exact h1
  have h3 : aeval (algebraMap (𝓞 F) F a) (f.scaleRoots p) = 0 := by
    rw [Polynomial.aeval_algebraMap_apply, h2, map_zero]
  have hpF : (algebraMap ℤ F p) ≠ 0 := by simpa using hp
  set β : F := algebraMap (𝓞 F) F a / algebraMap ℤ F p with hβdef
  have hβa : algebraMap ℤ F p * β = algebraMap (𝓞 F) F a := by
    rw [hβdef]; field_simp
  have h4 : eval₂ (algebraMap ℤ F) β f = 0 := by
    have e := Polynomial.scaleRoots_eval₂_mul (p := f) (algebraMap ℤ F) β p
    rw [hβa, ← aeval_def, h3] at e
    exact (mul_eq_zero.mp e.symm).resolve_left (pow_ne_zero _ hpF)
  have hβ : IsIntegral ℤ β := ⟨f, hfm, h4⟩
  let y : 𝓞 F := ⟨β, hβ⟩
  have hy : p • y = a := by
    apply RingOfIntegers.coe_injective
    rw [map_zsmul, zsmul_eq_mul]
    have : algebraMap (𝓞 F) F y = β := rfl
    rw [this, ← hβa]
    simp
  intro i
  refine ⟨b.repr y i, ?_⟩
  rw [← hy, map_zsmul, Finsupp.smul_apply, smul_eq_mul]

/- English proof (translation)
Introduce `F _ _ X _ _ _ ρ k _ ι _ b w hw hyp`. Assume the negation of the conclusion as `hX`. Use `haveI : Nontrivial X := Module.finrank_pos_iff.mp (Nat.pos_of_ne_zero hX)`. Choose the witnesses or unpack the hypotheses as in `⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Conclude with `hw (funext hc)`. Use `set B := Module.Free.chooseBasis ℤ X`. Establish `key : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X), ∑ i, (B.repr (ρ (b i) χ) r) • w i = 0`. Introduce `χ r`.

Use `hyp ((Int.castAddHom k).comp (B.coord r).toAddMonoidHom) χ` as an intermediate fact. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[zsmul_eq_mul, mul_comm]`. Establish `lin : ∀ (e : ι → ℤ) (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X), B.repr (ρ (∑ i, e i • b i) χ) r = ∑ i, e i * B.repr (ρ (b i) χ) r`.

Introduce `e χ r`. Simplify using `[map_sum, map_zsmul, LinearMap.sum_apply, Finsupp.finset_sum_apply]`. Break down `CharP.char_is_prime_or_zero k (ringChar k) with hp | hp` into its components or cases. Use `set p := ringChar k with hpdef haveI : Fact p.Prime := ⟨hp⟩ haveI : CharP k p := ringChar.charP k`. Use `letI : Algebra (ZMod p) k := ZMod.algebra k p`.

Choose the witnesses or unpack the hypotheses as in `⟨π, hπ⟩ : ∃ π : Module.Dual (ZMod p) k, π (w i0) ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hi0 ((Module.forall_dual_apply_eq_zero_iff (ZMod p) (w i0)).mp hc)`. Use `set e : ι → ℤ := fun i => ((π (w i)).val : ℤ) with hedef`.

Establish `hdiv : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X), (p : ℤ) ∣ B.repr (ρ (∑ i, e i • b i) χ) r`. Introduce `χ r`. Rewrite using `[lin, ← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `congrArg π (key χ r)` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`.

Rewrite using `[← this]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, zsmul_eq_mul, hedef]`. Simplify using `[ZMod.natCast_zmod_val, mul_comm]`.

Establish `h` using `GlobalTheory.dvd_coord_of_action_dvd F X ρ ι b p (by exact_mod_cast hp.ne_zero) _ hdiv i0`. Rewrite `h` using `[Module.Basis.repr_sum_self]`. Apply `hπ` to reduce the goal to its premises. Rewrite using `[← ZMod.natCast_zmod_val (π (w i0))]`. Establish `h' : ((((π (w i0)).val : ℕ) : ℤ) : ZMod p) = 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h`.

Conclude with `h'` after adjusting the coercions. Use `haveI : CharZero k := by`. Use `ringChar.charP k` as an intermediate fact. Rewrite `this` using `[hp]`. Conclude with `CharP.charP_to_charZero k`.

Use `letI : Algebra ℚ k := DivisionRing.toRatAlgebra`. Choose the witnesses or unpack the hypotheses as in `⟨π, hπ⟩ : ∃ π : Module.Dual ℚ k, π (w i0) ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hi0 ((Module.forall_dual_apply_eq_zero_iff ℚ (w i0)).mp hc)`.

Use `set c : ι → ℚ := fun i => π (w i) with hcdef`. Use `set e : ι → ℤ := fun i => (c i).num * ∏ j ∈ Finset.univ.erase i, ((c j).den : ℤ) with hedef`. Establish `he : ∀ i, (e i : ℚ) = c i * ∏ j, ((c j).den : ℚ)`. Introduce `i`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← mul_assoc, Rat.mul_den_eq_num, hedef]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hzero : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X), B.repr (ρ (∑ i, e i • b i) χ) r = 0`. Introduce `χ r`. Rewrite using `[lin]`.

Use `congrArg π (key χ r)` as an intermediate fact. Rewrite `this` using `[map_sum, map_zero]`. Simplify using `only [map_zsmul] at this`. Establish `h2 : ((∑ i, e i * B.repr (ρ (b i) χ) r : ℤ) : ℚ) = (∏ j, ((c j).den : ℚ)) * ∑ i, (B.repr (ρ (b i) χ) r) • π (w i)`. Use `push_cast`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[he, zsmul_eq_mul, hcdef]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[this, mul_zero]`.

Conclude with `h2` after adjusting the coercions. Establish `hρ : ρ (∑ i, e i • b i) = 0`. Use extensionality with `χ`. Simplify using `only [LinearMap.zero_apply]`. Conclude with `B.ext_elem fun r => by rw [hzero, map_zero, Finsupp.zero_apply]`.

Establish `ha : (∑ i, e i • b i) = 0` using `GlobalTheory.ringOfIntegers_action_injective F X ρ (by rw [hρ, map_zero])`. Establish `h0` using `congrArg (fun x => b.repr x i0) ha`. Simplify using `only [Module.Basis.repr_sum_self, map_zero, Finsupp.zero_apply] at h0`. Establish `hc0 : c i0 ≠ 0` using `hπ`. Establish `: (e i0 : ℚ) ≠ 0`.

Rewrite using `[he]`. Conclude with `mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (c j).den_nz)`. Conclude with `this (by exact_mod_cast h0)`.
-/
theorem finrank_eq_zero_of_dual_killed : ∀ (F : Type) [Field F] [NumberField F] (X : Type)
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (ρ : 𝓞 F →+* Module.End ℤ X)
    (k : Type) [Field k] (ι : Type) [Fintype ι] (b : Module.Basis ι ℤ (𝓞 F)) (w : ι → k),
    w ≠ 0 → (∀ (l : X →+ k) (χ : X), ∑ i, w i * l (ρ (b i) χ) = 0) →
    Module.finrank ℤ X = 0 := by
  intro F _ _ X _ _ _ ρ k _ ι _ b w hw hyp
  classical
  by_contra hX
  haveI : Nontrivial X := Module.finrank_pos_iff.mp (Nat.pos_of_ne_zero hX)
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hw (funext hc)
  set B := Module.Free.chooseBasis ℤ X
  have key : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
      ∑ i, (B.repr (ρ (b i) χ) r) • w i = 0 := by
    intro χ r
    have := hyp ((Int.castAddHom k).comp (B.coord r).toAddMonoidHom) χ
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [zsmul_eq_mul, mul_comm]
  have lin : ∀ (e : ι → ℤ) (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
      B.repr (ρ (∑ i, e i • b i) χ) r = ∑ i, e i * B.repr (ρ (b i) χ) r := by
    intro e χ r
    simp [map_sum, map_zsmul, LinearMap.sum_apply, Finsupp.finset_sum_apply]
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · set p := ringChar k with hpdef
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharP k p := ringChar.charP k
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    obtain ⟨π, hπ⟩ : ∃ π : Module.Dual (ZMod p) k, π (w i0) ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hi0 ((Module.forall_dual_apply_eq_zero_iff (ZMod p) (w i0)).mp hc)
    set e : ι → ℤ := fun i => ((π (w i)).val : ℤ) with hedef
    have hdiv : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
        (p : ℤ) ∣ B.repr (ρ (∑ i, e i • b i) χ) r := by
      intro χ r
      rw [lin, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have := congrArg π (key χ r)
      rw [map_sum, map_zero] at this
      rw [← this]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, zsmul_eq_mul, hedef]
      simp [ZMod.natCast_zmod_val, mul_comm]
    have h := GlobalTheory.dvd_coord_of_action_dvd F X ρ ι b p (by exact_mod_cast hp.ne_zero) _ hdiv i0
    rw [Module.Basis.repr_sum_self] at h
    apply hπ
    rw [← ZMod.natCast_zmod_val (π (w i0))]
    have h' : ((((π (w i0)).val : ℕ) : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    exact_mod_cast h'
  · haveI : CharZero k := by
      have := ringChar.charP k; rw [hp] at this; exact CharP.charP_to_charZero k
    letI : Algebra ℚ k := DivisionRing.toRatAlgebra
    obtain ⟨π, hπ⟩ : ∃ π : Module.Dual ℚ k, π (w i0) ≠ 0 := by
      by_contra hc; push_neg at hc
      exact hi0 ((Module.forall_dual_apply_eq_zero_iff ℚ (w i0)).mp hc)
    set c : ι → ℚ := fun i => π (w i) with hcdef
    set e : ι → ℤ := fun i => (c i).num * ∏ j ∈ Finset.univ.erase i, ((c j).den : ℤ) with hedef
    have he : ∀ i, (e i : ℚ) = c i * ∏ j, ((c j).den : ℚ) := by
      intro i
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← mul_assoc, Rat.mul_den_eq_num, hedef]
      push_cast; rfl
    have hzero : ∀ (χ : X) (r : Module.Free.ChooseBasisIndex ℤ X),
        B.repr (ρ (∑ i, e i • b i) χ) r = 0 := by
      intro χ r
      rw [lin]
      have := congrArg π (key χ r)
      rw [map_sum, map_zero] at this
      simp only [map_zsmul] at this
      have h2 : ((∑ i, e i * B.repr (ρ (b i) χ) r : ℤ) : ℚ)
          = (∏ j, ((c j).den : ℚ)) * ∑ i, (B.repr (ρ (b i) χ) r) • π (w i) := by
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [he, zsmul_eq_mul, hcdef]; ring
      rw [this, mul_zero] at h2
      exact_mod_cast h2
    have hρ : ρ (∑ i, e i • b i) = 0 := by
      ext χ
      simp only [LinearMap.zero_apply]
      exact B.ext_elem fun r => by rw [hzero, map_zero, Finsupp.zero_apply]
    have ha : (∑ i, e i • b i) = 0 :=
      GlobalTheory.ringOfIntegers_action_injective F X ρ (by rw [hρ, map_zero])
    have h0 := congrArg (fun x => b.repr x i0) ha
    simp only [Module.Basis.repr_sum_self, map_zero, Finsupp.zero_apply] at h0
    have hc0 : c i0 ≠ 0 := hπ
    have : (e i0 : ℚ) ≠ 0 := by
      rw [he]
      exact mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (c j).den_nz)
    exact this (by exact_mod_cast h0)

end GlobalTheory
