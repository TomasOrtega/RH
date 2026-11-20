import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

/- English proof (translation)
Establish `hc : (commutator G).topologicalClosure ≤ A.a.ker`. Apply `Subgroup.topologicalClosure_minimal` to reduce the goal to its premises. Conclude with `Abelianization.commutator_subset_ker A.a`. Conclude with `(isClosed_singleton.preimage A.cont : IsClosed (A.a ⁻¹' {1}))`. Take `⟨n, hn⟩` from `CommGroup.mem_primaryComponent.mp hg`.

Establish `hpow : g ^ (l ^ n) ∈ (commutator G).topologicalClosure`. Rewrite `hn` using `[← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]`. Conclude with `hn`. Establish `h1 : A.a g ^ (l ^ n) = 1`. Rewrite using `[← map_pow]`.

Conclude with `hc hpow`. Establish `hx : (l ^ n) • Multiplicative.toAdd (A.a g) = 0`. Use `congrArg Multiplicative.toAdd h1` as an intermediate fact. Simplify `this` using `[toAdd_pow]`. Establish `hl : l ^ n ≠ 0` using `pow_ne_zero n (Fact.out : l.Prime).ne_zero`.

Break down `smul_eq_zero.mp hx with h | h` into its components or cases. Conclude with `absurd h hl`. Establish `e : A.a g = Multiplicative.ofAdd (Multiplicative.toAdd (A.a g))` using `rfl`. Rewrite using `[e, h]`. Both sides reduce to the same expression.
-/
private theorem a_mu (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (I : Subgroup G) (d : ℕ) (A : LocAb l G I d) (g : G) (hg : g ∈ muG l G) : A.a g = 1 := by
  have hc : (commutator G).topologicalClosure ≤ A.a.ker := by
    apply Subgroup.topologicalClosure_minimal
    · exact Abelianization.commutator_subset_ker A.a
    · exact (isClosed_singleton.preimage A.cont : IsClosed (A.a ⁻¹' {1}))
  obtain ⟨n, hn⟩ := CommGroup.mem_primaryComponent.mp hg
  have hpow : g ^ (l ^ n) ∈ (commutator G).topologicalClosure := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hn
    exact hn
  have h1 : A.a g ^ (l ^ n) = 1 := by
    rw [← map_pow]
    exact hc hpow
  have hx : (l ^ n) • Multiplicative.toAdd (A.a g) = 0 := by
    have := congrArg Multiplicative.toAdd h1
    simpa [toAdd_pow] using this
  have hl : l ^ n ≠ 0 := pow_ne_zero n (Fact.out : l.Prime).ne_zero
  rcases smul_eq_zero.mp hx with h | h
  · exact absurd h hl
  · have e : A.a g = Multiplicative.ofAdd (Multiplicative.toAdd (A.a g)) := rfl
    rw [e, h]
    rfl

/- English proof (translation)
Establish `key : ∀ x : R, x - 1 ∈ m → ∀ k : ℕ, x ^ (l ^ k) - 1 ∈ m ^ (k + 1)`. Introduce `x hx k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hx`. Consider the case `succ k ih`.

Establish `hy : x ^ (l ^ k) - 1 ∈ m` using `Ideal.pow_le_self (Nat.succ_ne_zero k) ih`. Establish `h1 : Ideal.Quotient.mk m (x ^ (l ^ k)) = 1`. Rewrite using `[← sub_eq_zero, ← map_one (Ideal.Quotient.mk m), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hy`. Establish `hS : (∑ i ∈ Finset.range l, (x ^ (l ^ k)) ^ i) ∈ m`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sum]`. Simplify using `only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`. Rewrite using `[← map_natCast (Ideal.Quotient.mk m), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hl`. Establish `e : x ^ (l ^ (k + 1)) - 1 = (∑ i ∈ Finset.range l, (x ^ (l ^ k)) ^ i) * (x ^ (l ^ k) - 1)`.

Rewrite using `[geom_sum_mul, ← pow_mul, ← pow_succ]`. Rewrite using `[e, pow_succ' m (k + 1)]`. Conclude with `Ideal.mul_mem_mul hS ih`. Establish `hk : ∀ g, A.a g = 1 → ∀ N : ℕ, ((δ g : Rˣ) : R) - 1 ∈ m ^ N`. Introduce `g hg N`.

Set `ρ : G →* (R ⧸ m ^ N)ˣ` to `(Units.map (Ideal.Quotient.mk (m ^ N)).toMonoidHom).comp δ`. Establish `hρ : ∀ g, ρ g = 1 ↔ ((δ g : Rˣ) : R) - 1 ∈ m ^ N`. Introduce `g`. Rewrite using `[Units.ext_iff]`. Use `show Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R) = 1 ↔ _`.

Rewrite using `[← map_one (Ideal.Quotient.mk (m ^ N)), Ideal.Quotient.eq]`. Establish `hko : IsOpen (ρ.ker : Set G)`. Establish `e : (ρ.ker : Set G) = (fun g => Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R)) ⁻¹' {1}`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]`.

Conclude with `Units.ext_iff`. Rewrite using `[e]`. Conclude with `hc N {1}`. Establish `hopen : IsOpen (ρ.rangeRestrict.ker : Set G)`. Rewrite using `[MonoidHom.ker_rangeRestrict]`.

Conclude with `hko`. Use `haveI : Finite ρ.range := by haveI := Subgroup.quotient_finite_of_isOpen ρ.ker hko`. Conclude with `Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ).toEquiv`. Establish `hp : IsPGroup l ρ.range`. Introduce and unpack `⟨_, g', rfl⟩`.

Use `⟨N, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ρ g' ^ l ^ N = 1`. Rewrite using `[← map_pow, hρ, map_pow, Units.val_pow_eq_pow_val]`. Conclude with `Ideal.pow_le_pow_right (Nat.le_succ N) (key _ (hr g') N)`.

Establish `hmu : muG l G ≤ ρ.rangeRestrict.ker`. Rewrite using `[MonoidHom.ker_rangeRestrict]`. Introduce `g' hg'`. Rewrite using `[MonoidHom.mem_ker]`. Use `show Units.map (Ideal.Quotient.mk (m ^ N)).toMonoidHom (δ g') = 1`.

Rewrite using `[hm g' hg', map_one]`. Use `A.univ ρ.range hp ρ.rangeRestrict hopen hmu (MonoidHom.mem_ker.mpr hg)` as an intermediate fact. Rewrite `this` using `[MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hρ]`. Conclude with `this`. Establish `hδ1 : ∀ g, A.a g = 1 → δ g = 1`.

Introduce `g hg`. Apply `Units.ext` to reduce the goal to its premises. Establish `h0` using `IsHausdorff.haus' (I := m) (((δ g : Rˣ) : R) - 1) (fun N => by`. Rewrite using `[SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]`. Conclude with `hk g hg N)`.

Conclude with `sub_eq_zero.mp h0`. Set `e` to `QuotientGroup.quotientKerEquivOfSurjective A.a A.surj`. Set `χ0 : G ⧸ A.a.ker →* Rˣ` to `QuotientGroup.lift A.a.ker δ (fun g hg => MonoidHom.mem_ker.mpr (hδ1 g (MonoidHom.mem_ker.mp hg)))`. Set `χ` to `χ0.comp e.symm.toMonoidHom`. Establish `hχ : ∀ g, χ (A.a g) = δ g`.

Introduce `g`. Establish `h' : e.symm (A.a g) = (g : G ⧸ A.a.ker)`. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[MulEquiv.apply_symm_apply]`. Both sides reduce to the same expression.

Use `show χ0 (e.symm (A.a g)) = δ g`. Rewrite using `[h']`. Both sides reduce to the same expression. Use `⟨χ, ?_, hχ⟩` and prove the remaining obligations. Introduce `N s`.

Establish `hcl : IsClosed (A.a '' ((fun g => Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R)) ⁻¹' s)ᶜ)` using `A.cont.isClosedMap _ (hc N s).isClosed_compl`. Establish `heq : ((fun x => Ideal.Quotient.mk (m ^ N) ((χ x : Rˣ) : R)) ⁻¹' s)ᶜ = A.a '' ((fun g => Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R)) ⁻¹' s)ᶜ`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Take `⟨g, rfl⟩` from `A.surj x`. Conclude with `⟨g, by simpa [hχ] using hx, rfl⟩`. Introduce and unpack `⟨g, hg, rfl⟩`. Simplify `hg` using `[hχ]`. Rewrite `hcl` using `[← heq]`.

Conclude with `isClosed_compl_iff.mp hcl`.
-/
private theorem factor (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (I : Subgroup G) (d : ℕ) (A : LocAb l G I d) (R : Type) [CommRing R] (m : Ideal R)
    [IsHausdorff m R] (hl : (l : R) ∈ m) (δ : G →* Rˣ) (hc : AdicCont m fun g => ((δ g : Rˣ) : R))
    (hr : ∀ g, ((δ g : Rˣ) : R) - 1 ∈ m) (hm : ∀ g ∈ muG l G, δ g = 1) :
    ∃ χ : Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l]) →* Rˣ, AdicCont m (fun x => ((χ x : Rˣ) : R)) ∧
      ∀ g, χ (A.a g) = δ g := by
  classical
  have key : ∀ x : R, x - 1 ∈ m → ∀ k : ℕ, x ^ (l ^ k) - 1 ∈ m ^ (k + 1) := by
    intro x hx k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have hy : x ^ (l ^ k) - 1 ∈ m := Ideal.pow_le_self (Nat.succ_ne_zero k) ih
      have h1 : Ideal.Quotient.mk m (x ^ (l ^ k)) = 1 := by
        rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk m), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        exact hy
      have hS : (∑ i ∈ Finset.range l, (x ^ (l ^ k)) ^ i) ∈ m := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
        simp only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        rw [← map_natCast (Ideal.Quotient.mk m), Ideal.Quotient.eq_zero_iff_mem]
        exact hl
      have e : x ^ (l ^ (k + 1)) - 1 = (∑ i ∈ Finset.range l, (x ^ (l ^ k)) ^ i) * (x ^ (l ^ k) - 1) := by
        rw [geom_sum_mul, ← pow_mul, ← pow_succ]
      rw [e, pow_succ' m (k + 1)]
      exact Ideal.mul_mem_mul hS ih
  have hk : ∀ g, A.a g = 1 → ∀ N : ℕ, ((δ g : Rˣ) : R) - 1 ∈ m ^ N := by
    intro g hg N
    let ρ : G →* (R ⧸ m ^ N)ˣ := (Units.map (Ideal.Quotient.mk (m ^ N)).toMonoidHom).comp δ
    have hρ : ∀ g, ρ g = 1 ↔ ((δ g : Rˣ) : R) - 1 ∈ m ^ N := by
      intro g
      rw [Units.ext_iff]
      show Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R) = 1 ↔ _
      rw [← map_one (Ideal.Quotient.mk (m ^ N)), Ideal.Quotient.eq]
    have hko : IsOpen (ρ.ker : Set G) := by
      have e : (ρ.ker : Set G) = (fun g => Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R)) ⁻¹' {1} := by
        ext g
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
        exact Units.ext_iff
      rw [e]
      exact hc N {1}
    have hopen : IsOpen (ρ.rangeRestrict.ker : Set G) := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hko
    haveI : Finite ρ.range := by
      haveI := Subgroup.quotient_finite_of_isOpen ρ.ker hko
      exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ).toEquiv
    have hp : IsPGroup l ρ.range := by
      rintro ⟨_, g', rfl⟩
      refine ⟨N, ?_⟩
      apply Subtype.ext
      show ρ g' ^ l ^ N = 1
      rw [← map_pow, hρ, map_pow, Units.val_pow_eq_pow_val]
      exact Ideal.pow_le_pow_right (Nat.le_succ N) (key _ (hr g') N)
    have hmu : muG l G ≤ ρ.rangeRestrict.ker := by
      rw [MonoidHom.ker_rangeRestrict]
      intro g' hg'
      rw [MonoidHom.mem_ker]
      show Units.map (Ideal.Quotient.mk (m ^ N)).toMonoidHom (δ g') = 1
      rw [hm g' hg', map_one]
    have := A.univ ρ.range hp ρ.rangeRestrict hopen hmu (MonoidHom.mem_ker.mpr hg)
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hρ] at this
    exact this
  have hδ1 : ∀ g, A.a g = 1 → δ g = 1 := by
    intro g hg
    apply Units.ext
    have h0 := IsHausdorff.haus' (I := m) (((δ g : Rˣ) : R) - 1) (fun N => by
      rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
      exact hk g hg N)
    exact sub_eq_zero.mp h0
  let e := QuotientGroup.quotientKerEquivOfSurjective A.a A.surj
  let χ0 : G ⧸ A.a.ker →* Rˣ := QuotientGroup.lift A.a.ker δ
    (fun g hg => MonoidHom.mem_ker.mpr (hδ1 g (MonoidHom.mem_ker.mp hg)))
  let χ := χ0.comp e.symm.toMonoidHom
  have hχ : ∀ g, χ (A.a g) = δ g := by
    intro g
    have h' : e.symm (A.a g) = (g : G ⧸ A.a.ker) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    show χ0 (e.symm (A.a g)) = δ g
    rw [h']
    rfl
  refine ⟨χ, ?_, hχ⟩
  intro N s
  have hcl : IsClosed (A.a '' ((fun g => Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R)) ⁻¹' s)ᶜ) :=
    A.cont.isClosedMap _ (hc N s).isClosed_compl
  have heq : ((fun x => Ideal.Quotient.mk (m ^ N) ((χ x : Rˣ) : R)) ⁻¹' s)ᶜ =
      A.a '' ((fun g => Ideal.Quotient.mk (m ^ N) ((δ g : Rˣ) : R)) ⁻¹' s)ᶜ := by
    ext x
    constructor
    · intro hx
      obtain ⟨g, rfl⟩ := A.surj x
      exact ⟨g, by simpa [hχ] using hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      simpa [hχ] using hg
  rw [← heq] at hcl
  exact isClosed_compl_iff.mp hcl

/- English proof (translation)
Introduce `l _ F O _ _ _ _ _ _ _ n r d A R _ _ _ v i ψ₀ h0 ψ`. Use `haveI hcomp : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)`. Establish `hl : (l : R) ∈ maximalIdeal R`. Rewrite using `[← res_eq_zero_iff O R, map_natCast, CharP.cast_eq_zero]`. Prove the components needed by the constructor for the conclusion.

Introduce `hψ`. Set `δ : F.Gv v →* Rˣ` to `ψ * ψ₀⁻¹`. Establish `hδc : AdicCont (maximalIdeal R) (fun g => ((δ g : Rˣ) : R))`. Introduce `N`. Establish `hinv : ∀ u : Rˣ, Ring.inverse (Ideal.Quotient.mk (maximalIdeal R ^ N) (u : R)) = Ideal.Quotient.mk (maximalIdeal R ^ N) ((u⁻¹ : Rˣ) : R)`.

Introduce `u`. Establish `e : Ideal.Quotient.mk (maximalIdeal R ^ N) (u : R) = ((Units.map (Ideal.Quotient.mk (maximalIdeal R ^ N)).toMonoidHom u : (R ⧸ maximalIdeal R ^ N)ˣ) : R ⧸ maximalIdeal R ^ N)` using `rfl`. Rewrite using `[e, Ring.inverse_unit]`. Both sides reduce to the same expression. Establish `h1` using `hψ.cont N`.

Establish `h2 : IsLocallyConstant (fun g => Ring.inverse (Ideal.Quotient.mk (maximalIdeal R ^ N) ((ψ₀ g : Rˣ) : R)))` using `(h0.cont N).comp (Ring.inverse : R ⧸ maximalIdeal R ^ N → R ⧸ maximalIdeal R ^ N)`. Use `h1.mul h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using `only [Pi.mul_apply, hinv, δ, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_mul]`. Establish `hδr : ∀ g, ((δ g : Rˣ) : R) - 1 ∈ maximalIdeal R`.

Introduce `g`. Rewrite using `[← res_eq_zero_iff O R, map_sub, map_one]`. Establish `e3 : res O R ((ψ₀ g : Rˣ) : R) * res O R (((ψ₀ g)⁻¹ : Rˣ) : R) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Simplify using `only [δ, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_mul]`.

Rewrite using `[hψ.red g, ← h0.red g, e3, sub_self]`. Establish `hδm : ∀ g ∈ muG l (F.Gv v), δ g = 1`. Introduce `g hg`. Establish `e1` using `hψ.mu ⟨g, hg⟩`. Establish `e2` using `h0.mu ⟨g, hg⟩`.

Establish `hh : ψ g = ψ₀ g` using `Units.ext (e1.trans e2.symm)`. Simplify using `only [δ, MonoidHom.mul_apply, MonoidHom.inv_apply, hh, mul_inv_cancel]`. Take `⟨χ, hχc, hχ⟩` from `factor l (F.Gv v) (F.Iv v) (d v) (A v) R (maximalIdeal R) hl δ hδc hδr hδm`. Use `⟨χ, hχc, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`.

Take `⟨g, rfl⟩` from `(A v).surj x`. Rewrite using `[hχ g]`. Use `hδr g` as an intermediate fact. Rewrite `this` using `[← res_eq_zero_iff O R, map_sub, map_one, sub_eq_zero]`. Conclude with `this`.

Use `MonoidHom.ext fun g => ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.mul_apply, MonoidHom.comp_apply, hχ g]`. Simplify using `only [δ, MonoidHom.mul_apply, MonoidHom.inv_apply]`. Rewrite using `[mul_comm (ψ g), mul_inv_cancel_left]`. Introduce and unpack `⟨χ, hχc, hχr, rfl⟩`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `N`. Establish `h1` using `h0.cont N`. Establish `h2 : IsLocallyConstant (fun g => Ideal.Quotient.mk (maximalIdeal R ^ N) ((χ ((A v).a g) : Rˣ) : R))` using `(hχc N).comp_continuous (A v).cont`. Use `h1.mul h2 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `g`. Simplify using `only [Pi.mul_apply, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, map_mul]`. Introduce `g`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, map_mul, hχr, mul_one]`. Conclude with `h0.red g`.

Introduce `g`. Establish `ha` using `a_mu l (F.Gv v) (F.Iv v) (d v) (A v) g g.2`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.comp_apply, ha, map_one, mul_one]`. Conclude with `h0.mu g`.
-/
theorem UpperTheory.V.W.lam_factor :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (n : ℕ) (r : Resid F O n) (d : F.Vl → ℕ) (A : ∀ v, LocAb l (F.Gv v) (F.Iv v) (d v)) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (v : F.Vl) (i : Fin n) (ψ₀ : F.Gv v →* Rˣ), r.IsPsi v i ψ₀ → ∀ ψ : F.Gv v →* Rˣ,
      r.IsPsi v i ψ ↔ ∃ χ : Multiplicative ((Fin (d v) → ℤ_[l]) × ℤ_[l]) →* Rˣ, AdicCont (maximalIdeal R) (fun x => ((χ x : Rˣ) : R)) ∧ (∀ x, res O R (χ x) = 1) ∧ ψ = ψ₀ * χ.comp (A v).a := by
  intro l _ F O _ _ _ _ _ _ _ n r d A R _ _ _ v i ψ₀ h0 ψ
  haveI hcomp : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  have hl : (l : R) ∈ maximalIdeal R := by
    rw [← res_eq_zero_iff O R, map_natCast, CharP.cast_eq_zero]
  constructor
  · intro hψ
    let δ : F.Gv v →* Rˣ := ψ * ψ₀⁻¹
    have hδc : AdicCont (maximalIdeal R) (fun g => ((δ g : Rˣ) : R)) := by
      intro N
      have hinv : ∀ u : Rˣ, Ring.inverse (Ideal.Quotient.mk (maximalIdeal R ^ N) (u : R)) =
          Ideal.Quotient.mk (maximalIdeal R ^ N) ((u⁻¹ : Rˣ) : R) := by
        intro u
        have e : Ideal.Quotient.mk (maximalIdeal R ^ N) (u : R) =
            ((Units.map (Ideal.Quotient.mk (maximalIdeal R ^ N)).toMonoidHom u : (R ⧸ maximalIdeal R ^ N)ˣ) :
              R ⧸ maximalIdeal R ^ N) := rfl
        rw [e, Ring.inverse_unit]
        rfl
      have h1 := hψ.cont N
      have h2 : IsLocallyConstant (fun g => Ring.inverse
          (Ideal.Quotient.mk (maximalIdeal R ^ N) ((ψ₀ g : Rˣ) : R))) :=
        (h0.cont N).comp (Ring.inverse : R ⧸ maximalIdeal R ^ N → R ⧸ maximalIdeal R ^ N)
      convert h1.mul h2 using 1
      funext g
      simp only [Pi.mul_apply, hinv, δ, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_mul]
    have hδr : ∀ g, ((δ g : Rˣ) : R) - 1 ∈ maximalIdeal R := by
      intro g
      rw [← res_eq_zero_iff O R, map_sub, map_one]
      have e3 : res O R ((ψ₀ g : Rˣ) : R) * res O R (((ψ₀ g)⁻¹ : Rˣ) : R) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      simp only [δ, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_mul]
      rw [hψ.red g, ← h0.red g, e3, sub_self]
    have hδm : ∀ g ∈ muG l (F.Gv v), δ g = 1 := by
      intro g hg
      have e1 := hψ.mu ⟨g, hg⟩
      have e2 := h0.mu ⟨g, hg⟩
      have hh : ψ g = ψ₀ g := Units.ext (e1.trans e2.symm)
      simp only [δ, MonoidHom.mul_apply, MonoidHom.inv_apply, hh, mul_inv_cancel]
    obtain ⟨χ, hχc, hχ⟩ := factor l (F.Gv v) (F.Iv v) (d v) (A v) R (maximalIdeal R) hl δ hδc hδr hδm
    refine ⟨χ, hχc, ?_, ?_⟩
    · intro x
      obtain ⟨g, rfl⟩ := (A v).surj x
      rw [hχ g]
      have := hδr g
      rw [← res_eq_zero_iff O R, map_sub, map_one, sub_eq_zero] at this
      exact this
    · refine MonoidHom.ext fun g => ?_
      rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hχ g]
      simp only [δ, MonoidHom.mul_apply, MonoidHom.inv_apply]
      rw [mul_comm (ψ g), mul_inv_cancel_left]
  · rintro ⟨χ, hχc, hχr, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro N
      have h1 := h0.cont N
      have h2 : IsLocallyConstant (fun g => Ideal.Quotient.mk (maximalIdeal R ^ N)
          ((χ ((A v).a g) : Rˣ) : R)) := (hχc N).comp_continuous (A v).cont
      convert h1.mul h2 using 1
      funext g
      simp only [Pi.mul_apply, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, map_mul]
    · intro g
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, map_mul, hχr, mul_one]
      exact h0.red g
    · intro g
      have ha := a_mu l (F.Gv v) (F.Iv v) (d v) (A v) g g.2
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, ha, map_one, mul_one]
      exact h0.mu g
