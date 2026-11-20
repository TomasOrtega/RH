import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PlusEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

/- English proof (translation)
Establish `key` using `h (n : 𝓞 F)`. Simplify using `using key`.
-/
private theorem nat_place {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω}
    {v : W.Plc F} (h : IsPlaceOver A v) (n : ℕ) : A.valuation (n : Ω) < 1 ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  have key := h (n : 𝓞 F)
  simpa using key

open scoped Pointwise in
/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T`. Take `⟨hF, ⟨φ, hφ, -⟩, -⟩` from `galEq T`. Establish `hfix : ∀ (g : G T.F Ω) (y : W.Lp T.L), g (algebraMap (W.Lp T.L) Ω y) = algebraMap (W.Lp T.L) Ω y`. Introduce `g y`. Establish `hy` using `(hF (algebraMap (W.Lp T.L) Ω y)).2 ⟨y, rfl⟩`.

Conclude with `g.commutes ⟨_, hy⟩`. Establish `hmove : ∀ (g : G T.F Ω) {A B : ValuationSubring Ω}, (∀ x, g x ∈ B ↔ x ∈ A) → ∀ {v : W.Plc (W.Lp T.L)}, IsPlaceOver A v → IsPlaceOver B v`. Introduce `g A B hg v h x`. Establish `key` using `val_lt_one (σ := g.toRingEquiv) hg (algebraMap (W.Lp T.L) Ω x)`. Establish `hx : g.toRingEquiv (algebraMap (W.Lp T.L) Ω x) = algebraMap (W.Lp T.L) Ω x` using `hfix g x`.

Rewrite `key` using `[hx]`. Rewrite using `[key]`. Conclude with `h x`. Establish `hA : ∀ v : W.Vl l T.L, ∃ A : ValuationSubring Ω, IsPlaceOver A v.1` using `fun v => exists_isPlaceOver Ω v.1`. Use `choose A hAv using hA`.

Establish `hAl : ∀ v, (A v).valuation (l : Ω) < 1` using `fun v => (nat_place (hAv v) l).2 v.2`. Use `choose e he using fun v => (T.cover (A v) (hAl v)).exists`. Establish `hover : ∀ v, IsPlaceOver (T.pl (e v)) v.1`. Introduce `v`. Take `⟨g, hg⟩` from `he v`.

Use `hmove g⁻¹ ?_ (hAv v)` and prove the remaining obligations. Introduce `x`. Rewrite using `[← hg]`. Simplify using the standard rewrite rules. Use `⟨Equiv.ofBijective e ⟨?_, ?_⟩, hover⟩` and prove the remaining obligations.

Introduce `v v' hvv`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1` using `hover v`. Establish `h2` using `hover v'`. Rewrite `h1` using `[hvv]`.

Conclude with `eq_of_isPlaceOver h1 h2`. Introduce `w`. Establish `hne : T.pl w ≠ ⊤`. Introduce `htop`. Conclude with `((places (W.Lp T.L) Ω l (T.pl w)).2.1 htop).2 (T.ovl w)`.

Take `⟨v0, hv0⟩` from `(places (W.Lp T.L) Ω l (T.pl w)).1 hne`. Establish `hv0l : (l : 𝓞 (W.Lp T.L)) ∈ v0.asIdeal` using `(nat_place hv0 l).1 (T.ovl w)`. Use `⟨⟨v0, hv0l⟩, ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `exists_smul_eq_of_isPlaceOver hv0 (hAv ⟨v0, hv0l⟩)`. Apply `(T.cover (A ⟨v0, hv0l⟩) (hAl _)).unique (he _)` to reduce the goal to its premises.

Use `⟨φ σ, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hφ, ← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← AlgEquiv.smul_def, inv_smul_smul]`.
-/
theorem UpperTheory.V.Ws.Lk.placesEq :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), ∃ e : W.Vl l T.L ≃ T.ι, ∀ v : W.Vl l T.L, IsPlaceOver (T.pl (e v)) v.1 := by
  intro Ω _ _ _ l _ c D T
  obtain ⟨hF, ⟨φ, hφ, -⟩, -⟩ := galEq T
  have hfix : ∀ (g : G T.F Ω) (y : W.Lp T.L), g (algebraMap (W.Lp T.L) Ω y) = algebraMap (W.Lp T.L) Ω y := by
    intro g y
    have hy := (hF (algebraMap (W.Lp T.L) Ω y)).2 ⟨y, rfl⟩
    exact g.commutes ⟨_, hy⟩
  have hmove : ∀ (g : G T.F Ω) {A B : ValuationSubring Ω}, (∀ x, g x ∈ B ↔ x ∈ A) →
      ∀ {v : W.Plc (W.Lp T.L)}, IsPlaceOver A v → IsPlaceOver B v := by
    intro g A B hg v h x
    have key := val_lt_one (σ := g.toRingEquiv) hg (algebraMap (W.Lp T.L) Ω x)
    have hx : g.toRingEquiv (algebraMap (W.Lp T.L) Ω x) = algebraMap (W.Lp T.L) Ω x := hfix g x
    rw [hx] at key
    rw [key]
    exact h x
  have hA : ∀ v : W.Vl l T.L, ∃ A : ValuationSubring Ω, IsPlaceOver A v.1 := fun v => exists_isPlaceOver Ω v.1
  choose A hAv using hA
  have hAl : ∀ v, (A v).valuation (l : Ω) < 1 := fun v => (nat_place (hAv v) l).2 v.2
  choose e he using fun v => (T.cover (A v) (hAl v)).exists
  have hover : ∀ v, IsPlaceOver (T.pl (e v)) v.1 := by
    intro v
    obtain ⟨g, hg⟩ := he v
    refine hmove g⁻¹ ?_ (hAv v)
    intro x
    rw [← hg]
    simp
  refine ⟨Equiv.ofBijective e ⟨?_, ?_⟩, hover⟩
  · intro v v' hvv
    apply Subtype.ext
    have h1 := hover v
    have h2 := hover v'
    rw [hvv] at h1
    exact eq_of_isPlaceOver h1 h2
  · intro w
    have hne : T.pl w ≠ ⊤ := by
      intro htop
      exact ((places (W.Lp T.L) Ω l (T.pl w)).2.1 htop).2 (T.ovl w)
    obtain ⟨v0, hv0⟩ := (places (W.Lp T.L) Ω l (T.pl w)).1 hne
    have hv0l : (l : 𝓞 (W.Lp T.L)) ∈ v0.asIdeal := (nat_place hv0 l).1 (T.ovl w)
    refine ⟨⟨v0, hv0l⟩, ?_⟩
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hv0 (hAv ⟨v0, hv0l⟩)
    apply (T.cover (A ⟨v0, hv0l⟩) (hAl _)).unique (he _)
    refine ⟨φ σ, fun x => ?_⟩
    rw [hφ, ← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← AlgEquiv.smul_def, inv_smul_smul]
