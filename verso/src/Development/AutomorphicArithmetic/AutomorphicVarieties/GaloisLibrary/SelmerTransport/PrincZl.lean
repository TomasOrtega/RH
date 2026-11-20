import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.EqOneOfMemPrincOne
import GroundTheory.GlobalFields.CyclotomicCharacters.PadicUnitsLog

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

/- English proof (translation)
Introduce `l _ H hHc hHp hH1`. Establish `tors : ∀ u ∈ H, IsOfFinOrder u → u = 1`. Introduce `u hu hfin`. Establish `hpr` using `hHp hu`. Establish `hmem : u ∈ CommGroup.torsion ℤ_[l]ˣ` using `(CommGroup.mem_torsion u).2 hfin`.

Distinguish the cases in `h2 : l = 2`. Substitute `h2` using the available equality. Break down `(GroundTheory.Global.Cyclotomic.mem_torsion_two_iff u).1 hmem with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction.

Rewrite `hpr` using `[KStar.TotallyRealRoots.mem_princ, h]`. Take `⟨c, hc⟩` from `hpr`. Establish `hc2 : (2 : ℤ_[2]) * (1 + 2 * c) = 0`. Move the coercions through the operations in `[qExp] at hc`. Take the linear combination `-hc`.

Establish `h2ne : (2 : ℤ_[2]) ≠ 0` using `two_ne_zero`. Establish `h1 : (1 : ℤ_[2]) + 2 * c = 0` using `(mul_eq_zero.1 hc2).resolve_left h2ne`. Establish `hn : ‖(2 : ℤ_[2]) * c‖ = 1`. Rewrite using `[show (2 : ℤ_[2]) * c = -1 by linear_combination h1, norm_neg, norm_one]`. Establish `hn2 : ‖(2 : ℤ_[2])‖ = 1 / 2`.

Use `PadicInt.norm_p (p := 2)` as an intermediate fact. Evaluate the numerical expressions using `at this ⊢`. Conclude with `this`. Rewrite `hn` using `[norm_mul, hn2]`. Use `PadicInt.norm_le_one c` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht : u ^ GroundTheory.Global.Cyclotomic.torsionExponent l = 1` using `(GroundTheory.Global.Cyclotomic.mem_torsion_iff l u).1 hmem`. Establish `hq : qExp l = 1` using `by simp [qExp, h2]`. Rewrite `hpr` using `[hq]`. Establish `hte : GroundTheory.Global.Cyclotomic.torsionExponent l = l - 1`.

Simplify using `[GroundTheory.Global.Cyclotomic.torsionExponent, h2]`. Rewrite `ht` using `[hte]`. Establish `hl` using `(Fact.out : l.Prime).two_le`. Use `KStar.TotallyRealRoots.eq_one_of_mem_princ_one (o := l - 1) ?_ ?_ hpr` and prove the remaining obligations. Introduce `hd`.

Use `Nat.le_of_dvd (by omega) hd` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[mem_rootsOfUnity]`. Conclude with `ht`. Use `⟨?_, tors⟩` and prove the remaining obligations.

Set `L : ℤ_[l]ˣ →* Multiplicative ℤ_[l]` to `GroundTheory.Global.Cyclotomic.padicUnitsLog l`. Establish `hker : L.ker = CommGroup.torsion ℤ_[l]ˣ` using `GroundTheory.Global.Cyclotomic.ker_padicUnitsLog l`. Set `f : H → ℤ_[l]` to `fun h => Multiplicative.toAdd (L h)`. Establish `hfc : Continuous f` using `(GroundTheory.Global.Cyclotomic.continuous_padicUnitsLog l).comp continuous_subtype_val`. Establish `hmul : ∀ a b : H, f (a * b) = f a + f b`.

Introduce `a b`. Simplify using `[f, L]`. Establish `hpow : ∀ (a : H) (n : ℤ), f (a ^ n) = n * f a`. Introduce `a n`. Simplify using `[f, L, zsmul_eq_mul]`.

Establish `hf1 : f 1 = 0` using `by simp [f, L]`. Establish `hinj : Function.Injective f`. Introduce `a b hab`. Establish `hL : L a = L b` using `hab`. Establish `hk : (a : ℤ_[l]ˣ) * (b : ℤ_[l]ˣ)⁻¹ ∈ L.ker`.

Rewrite using `[MonoidHom.mem_ker, map_mul, map_inv, hL, mul_inv_cancel]`. Rewrite `hk` using `[hker, CommGroup.mem_torsion]`. Use `tors _ (H.mul_mem a.2 (H.inv_mem b.2)) hk` as an intermediate fact. Conclude with `Subtype.ext (mul_inv_eq_one.1 this)`. Use `haveI : CompactSpace H := isCompact_iff_compactSpace.1 hHc.isCompact`.

Establish `hcl : IsClosed (Set.range f)` using `(isCompact_range hfc).isClosed`. Set `I : Ideal ℤ_[l]` to `{ carrier := Set.range f add_mem' := by`. Introduce and unpack `_ _ ⟨a, rfl⟩ ⟨b, rfl⟩`. Conclude with `⟨a * b, hmul a b⟩`. Use the proof step `zero_mem' := ⟨1, hf1⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c _ ⟨a, rfl⟩`. Establish `hm : Continuous (fun t : ℤ_[l] => t * f a)` using `continuous_mul_right (f a)`. Establish `hsub` using `hm.range_subset_closure_image_dense (PadicInt.denseRange_intCast (p := l))`. Establish `himg : (fun t : ℤ_[l] => t * f a) '' Set.range (Int.cast : ℤ → ℤ_[l]) ⊆ Set.range f`.

Introduce and unpack `_ ⟨_, ⟨n, rfl⟩, rfl⟩`. Conclude with `⟨a ^ n, hpow a n⟩`. Conclude with `closure_minimal himg hcl (hsub ⟨c, rfl⟩) }`. Establish `hI : ∀ y, y ∈ Set.range f ↔ ∃ c, c * Submodule.IsPrincipal.generator I = y`. Introduce `y`.

Establish `h : y ∈ I ↔ y ∈ Ideal.span {Submodule.IsPrincipal.generator I}`. Rewrite using `[Ideal.span_singleton_generator]`. Rewrite `h` using `[Ideal.mem_span_singleton']`. Conclude with `h`. Use `set g := Submodule.IsPrincipal.generator I with hgdef`.

Take `⟨a0, ha0⟩` from `(Subgroup.ne_bot_iff_exists_ne_one).1 hH1`. Establish `hg0 : g ≠ 0`. Introduce `hg`. Take `⟨c, hc⟩` from `(hI (f a0)).1 ⟨a0, rfl⟩`. Rewrite `hc` using `[hg, mul_zero, ← hf1]`.

Conclude with `ha0 (hinj hc).symm`. Set `e : H → ℤ_[l]` to `fun h => Classical.choose ((hI (f h)).1 ⟨h, rfl⟩)`. Establish `he : ∀ h, e h * g = f h` using `fun h => Classical.choose_spec ((hI (f h)).1 ⟨h, rfl⟩)`. Establish `hminj : Function.Injective (fun t : ℤ_[l] => t * g)` using `mul_left_injective₀ hg0`. Establish `hmemb` using `((continuous_mul_right g).isClosedEmbedding hminj).isEmbedding`.

Establish `hec : Continuous e`. Rewrite using `[hmemb.continuous_iff]`. Establish `: ((fun t : ℤ_[l] => t * g) ∘ e) = f` using `funext he`. Rewrite using `[this]`. Conclude with `hfc`.

Establish `hemul : ∀ a b : H, e (a * b) = e a + e b`. Introduce `a b`. Apply `hminj` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[he, add_mul, he, he, hmul]`.

Establish `heinj : Function.Injective e`. Introduce `a b hab`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[← he, ← he, hab]`. Establish `hesurj : Function.Surjective e`.

Introduce `c`. Take `⟨h, hh⟩` from `(hI (c * g)).2 ⟨c, rfl⟩`. Use `⟨h, hminj ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[he, hh]`.

Set `φ : H →* Multiplicative ℤ_[l]` to `MonoidHom.mk' (fun h => Multiplicative.ofAdd (e h)) (by`. Introduce `a b`. Rewrite using `[hemul]`. Use the proof step `rfl)`. Set `E : H ≃* Multiplicative ℤ_[l]` to `MulEquiv.ofBijective φ ⟨heinj, hesurj⟩`.

Establish `hEc : Continuous E` using `hec`. Set `Φ` to `Continuous.homeoOfEquivCompactToT2 (f := E.toEquiv) hEc`. Conclude with `⟨{ toMulEquiv := E, continuous_toFun := hEc, continuous_invFun := Φ.symm.continuous }⟩`.
-/
theorem UpperTheory.V.Base.princZl :
    ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup ℤ_[l]ˣ), IsClosed (H : Set ℤ_[l]ˣ) → H ≤ KStar.TotallyRealRoots.princ l (qExp l) → H ≠ ⊥ →
      Nonempty (H ≃ₜ* Multiplicative ℤ_[l]) ∧ ∀ u ∈ H, IsOfFinOrder u → u = 1 := by
  intro l _ H hHc hHp hH1
  have tors : ∀ u ∈ H, IsOfFinOrder u → u = 1 := by
    intro u hu hfin
    have hpr := hHp hu
    have hmem : u ∈ CommGroup.torsion ℤ_[l]ˣ := (CommGroup.mem_torsion u).2 hfin
    by_cases h2 : l = 2
    · subst h2
      rcases (GroundTheory.Global.Cyclotomic.mem_torsion_two_iff u).1 hmem with h | h
      · exact h
      · exfalso
        rw [KStar.TotallyRealRoots.mem_princ, h] at hpr
        obtain ⟨c, hc⟩ := hpr
        have hc2 : (2 : ℤ_[2]) * (1 + 2 * c) = 0 := by
          push_cast [qExp] at hc
          linear_combination -hc
        have h2ne : (2 : ℤ_[2]) ≠ 0 := two_ne_zero
        have h1 : (1 : ℤ_[2]) + 2 * c = 0 := (mul_eq_zero.1 hc2).resolve_left h2ne
        have hn : ‖(2 : ℤ_[2]) * c‖ = 1 := by
          rw [show (2 : ℤ_[2]) * c = -1 by linear_combination h1, norm_neg, norm_one]
        have hn2 : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
          have := PadicInt.norm_p (p := 2)
          norm_num at this ⊢
          exact this
        rw [norm_mul, hn2] at hn
        have := PadicInt.norm_le_one c
        linarith
    · have ht : u ^ GroundTheory.Global.Cyclotomic.torsionExponent l = 1 :=
        (GroundTheory.Global.Cyclotomic.mem_torsion_iff l u).1 hmem
      have hq : qExp l = 1 := by simp [qExp, h2]
      rw [hq] at hpr
      have hte : GroundTheory.Global.Cyclotomic.torsionExponent l = l - 1 := by
        simp [GroundTheory.Global.Cyclotomic.torsionExponent, h2]
      rw [hte] at ht
      have hl := (Fact.out : l.Prime).two_le
      refine KStar.TotallyRealRoots.eq_one_of_mem_princ_one (o := l - 1) ?_ ?_ hpr
      · intro hd
        have := Nat.le_of_dvd (by omega) hd
        omega
      · rw [mem_rootsOfUnity]
        exact ht
  refine ⟨?_, tors⟩
  classical
  let L : ℤ_[l]ˣ →* Multiplicative ℤ_[l] := GroundTheory.Global.Cyclotomic.padicUnitsLog l
  have hker : L.ker = CommGroup.torsion ℤ_[l]ˣ := GroundTheory.Global.Cyclotomic.ker_padicUnitsLog l
  let f : H → ℤ_[l] := fun h => Multiplicative.toAdd (L h)
  have hfc : Continuous f :=
    (GroundTheory.Global.Cyclotomic.continuous_padicUnitsLog l).comp continuous_subtype_val
  have hmul : ∀ a b : H, f (a * b) = f a + f b := by
    intro a b
    simp [f, L]
  have hpow : ∀ (a : H) (n : ℤ), f (a ^ n) = n * f a := by
    intro a n
    simp [f, L, zsmul_eq_mul]
  have hf1 : f 1 = 0 := by simp [f, L]
  have hinj : Function.Injective f := by
    intro a b hab
    have hL : L a = L b := hab
    have hk : (a : ℤ_[l]ˣ) * (b : ℤ_[l]ˣ)⁻¹ ∈ L.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hL, mul_inv_cancel]
    rw [hker, CommGroup.mem_torsion] at hk
    have := tors _ (H.mul_mem a.2 (H.inv_mem b.2)) hk
    exact Subtype.ext (mul_inv_eq_one.1 this)
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hHc.isCompact
  have hcl : IsClosed (Set.range f) := (isCompact_range hfc).isClosed
  let I : Ideal ℤ_[l] :=
    { carrier := Set.range f
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, hmul a b⟩
      zero_mem' := ⟨1, hf1⟩
      smul_mem' := by
        rintro c _ ⟨a, rfl⟩
        have hm : Continuous (fun t : ℤ_[l] => t * f a) := continuous_mul_right (f a)
        have hsub := hm.range_subset_closure_image_dense (PadicInt.denseRange_intCast (p := l))
        have himg : (fun t : ℤ_[l] => t * f a) '' Set.range (Int.cast : ℤ → ℤ_[l]) ⊆ Set.range f := by
          rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
          exact ⟨a ^ n, hpow a n⟩
        exact closure_minimal himg hcl (hsub ⟨c, rfl⟩) }
  have hI : ∀ y, y ∈ Set.range f ↔ ∃ c, c * Submodule.IsPrincipal.generator I = y := by
    intro y
    have h : y ∈ I ↔ y ∈ Ideal.span {Submodule.IsPrincipal.generator I} := by
      rw [Ideal.span_singleton_generator]
    rw [Ideal.mem_span_singleton'] at h
    exact h
  set g := Submodule.IsPrincipal.generator I with hgdef
  obtain ⟨a0, ha0⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hH1
  have hg0 : g ≠ 0 := by
    intro hg
    obtain ⟨c, hc⟩ := (hI (f a0)).1 ⟨a0, rfl⟩
    rw [hg, mul_zero, ← hf1] at hc
    exact ha0 (hinj hc).symm
  let e : H → ℤ_[l] := fun h => Classical.choose ((hI (f h)).1 ⟨h, rfl⟩)
  have he : ∀ h, e h * g = f h := fun h => Classical.choose_spec ((hI (f h)).1 ⟨h, rfl⟩)
  have hminj : Function.Injective (fun t : ℤ_[l] => t * g) := mul_left_injective₀ hg0
  have hmemb := ((continuous_mul_right g).isClosedEmbedding hminj).isEmbedding
  have hec : Continuous e := by
    rw [hmemb.continuous_iff]
    have : ((fun t : ℤ_[l] => t * g) ∘ e) = f := funext he
    rw [this]
    exact hfc
  have hemul : ∀ a b : H, e (a * b) = e a + e b := by
    intro a b
    apply hminj
    simp only
    rw [he, add_mul, he, he, hmul]
  have heinj : Function.Injective e := by
    intro a b hab
    apply hinj
    rw [← he, ← he, hab]
  have hesurj : Function.Surjective e := by
    intro c
    obtain ⟨h, hh⟩ := (hI (c * g)).2 ⟨c, rfl⟩
    refine ⟨h, hminj ?_⟩
    simp only
    rw [he, hh]
  let φ : H →* Multiplicative ℤ_[l] :=
    MonoidHom.mk' (fun h => Multiplicative.ofAdd (e h)) (by
      intro a b
      rw [hemul]
      rfl)
  let E : H ≃* Multiplicative ℤ_[l] := MulEquiv.ofBijective φ ⟨heinj, hesurj⟩
  have hEc : Continuous E := hec
  let Φ := Continuous.homeoOfEquivCompactToT2 (f := E.toEquiv) hEc
  exact ⟨{ toMulEquiv := E, continuous_toFun := hEc, continuous_invFun := Φ.symm.continuous }⟩
