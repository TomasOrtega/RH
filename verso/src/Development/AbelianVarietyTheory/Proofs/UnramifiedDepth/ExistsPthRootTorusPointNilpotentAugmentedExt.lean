import Mathlib

open Polynomial

namespace GlobalTheory.TorusRoot

/- English proof (translation)
Establish `hp0 : p ≠ 0` using `hp.out.ne_zero`. Use `haveI : Nontrivial A := π.toRingHom.domain_nontrivial`. Set `P : A[X]` to `X ^ p - C a.val`. Establish `hP : P.Monic` using `monic_X_pow_sub_C _ hp0`. Set `f : A →ₐ[Ω] AdjoinRoot P` to `IsScalarTower.toAlgHom Ω A (AdjoinRoot P)`.

Establish `hf : ∀ x, f x = AdjoinRoot.of P x` using `fun x => rfl`. Establish `hinj : Function.Injective f`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Rewrite `hx` using `[hf, ← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_zero]`.

Assume the negation of the conclusion as `hx0`. Use `hP.not_dvd_of_degree_lt (C_ne_zero.2 hx0) ?_ hx` and prove the remaining obligations. Rewrite using `[degree_C hx0, degree_X_pow_sub_C (Nat.pos_of_ne_zero hp0)]`. Conclude with `Nat.pos_of_ne_zero hp0` after adjusting the coercions. Establish `hev : P.eval₂ (π : A →+* Ω) 1 = 0`.

Simplify using `[P, eval₂_sub, ha]`. Set `g : AdjoinRoot P →+* Ω` to `AdjoinRoot.lift (π : A →+* Ω) 1 hev`. Establish `hg : ∀ x, g (f x) = π x` using `fun x => by`. Rewrite using `[hf]`. Conclude with `AdjoinRoot.lift_of hev`.

Establish `hgr : g (AdjoinRoot.root P) = 1` using `AdjoinRoot.lift_root hev`. Set `π' : AdjoinRoot P →ₐ[Ω] Ω` to `{ g with commutes' := fun c => by`. Establish `: algebraMap Ω (AdjoinRoot P) c = f (algebraMap Ω A c)` using `(f.commutes c).symm`. Express the relevant statement in the definitionally equal form `g _ = _`. Rewrite using `[this, hg, π.commutes] }`.

Establish `hroot : AdjoinRoot.root P ^ p = f a.val`. Establish `h` using `AdjoinRoot.eval₂_root P`. Simplify using `only [P, eval₂_sub, eval₂_X_pow, eval₂_C] at h`. Conclude with `sub_eq_zero.1 h`. Establish `hu : IsUnit (AdjoinRoot.root P)`.

Rewrite using `[← isUnit_pow_iff hp0, hroot]`. Conclude with `a.isUnit.map f`. Use `haveI : Nontrivial (AdjoinRoot P) := g.domain_nontrivial`. Use `haveI : CharP (AdjoinRoot P) p := charP_of_injective_algebraMap (algebraMap Ω (AdjoinRoot P)).injective p`. Use `⟨AdjoinRoot P, inferInstance, inferInstance, f, π', hu.unit, hinj, ?_, ?_, hgr, ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Conclude with `hg x`. Use `set I : Ideal (AdjoinRoot P) := (RingHom.ker π).map f with hI`. Establish `hIn : IsNilpotent I`. Take `⟨n, hn⟩` from `hπ`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[hI, ← Ideal.map_pow, hn]`. Conclude with `Ideal.map_bot`. Use `set J : Ideal (AdjoinRoot P) := Ideal.span {AdjoinRoot.root P - 1} with hJ`. Establish `hJn : IsNilpotent J`.

Take `⟨n, hn⟩` from `hIn`. Use `⟨p * n, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_mul, Ideal.zero_eq_bot, eq_bot_iff, ← Ideal.zero_eq_bot, ← hn]`. Apply `Ideal.pow_right_mono` to reduce the goal to its premises. Rewrite using `[hJ, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, sub_pow_char, hroot, one_pow, ← map_one f, ← map_sub]`.

Apply `Ideal.mem_map_of_mem` to reduce the goal to its premises. Rewrite using `[RingHom.mem_ker, map_sub, ha, map_one, sub_self]`. Take `⟨n, hn⟩` from `(Commute.all I J).isNilpotent_add hIn hJn`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.zero_eq_bot, eq_bot_iff, ← Ideal.zero_eq_bot, ← hn]`.

Apply `Ideal.pow_right_mono` to reduce the goal to its premises. Introduce `x hx`. Take `⟨q, rfl⟩` from `AdjoinRoot.mk_surjective x`. Take `⟨r, hr⟩ : (X - C 1 : A[X]) ∣ q - C (q.eval 1)` from `X_sub_C_dvd_sub_C_eval`. Establish `h1 : AdjoinRoot.mk P q = f (q.eval 1) + (AdjoinRoot.root P - 1) * AdjoinRoot.mk P r`.

Use `congrArg (AdjoinRoot.mk P) hr` as an intermediate fact. Simplify using `only [map_sub, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_one] at this`. Rewrite using `[hf, ← this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hx' : g (AdjoinRoot.mk P q) = 0` using `hx`.

Rewrite `hx'` using `[h1, map_add, map_mul, map_sub, hgr, map_one, sub_self, zero_mul, add_zero, hg]`. Rewrite using `[h1, Ideal.add_eq_sup]`. Conclude with `Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hx') (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))`. Use `ext`. Simplify using `using hroot`.
-/
theorem exists_root_one (Ω : Type) [Field Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p]
    (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω) (hπ : IsNilpotent (RingHom.ker π))
    (a : Aˣ) (ha : π a.val = 1) :
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω)
      (s : A'ˣ), Function.Injective f ∧ π'.comp f = π ∧ IsNilpotent (RingHom.ker π') ∧
      π' s.val = 1 ∧ s ^ p = Units.map (f : A →* A') a := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  haveI : Nontrivial A := π.toRingHom.domain_nontrivial
  let P : A[X] := X ^ p - C a.val
  have hP : P.Monic := monic_X_pow_sub_C _ hp0
  let f : A →ₐ[Ω] AdjoinRoot P := IsScalarTower.toAlgHom Ω A (AdjoinRoot P)
  have hf : ∀ x, f x = AdjoinRoot.of P x := fun x => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hf, ← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_zero] at hx
    by_contra hx0
    refine hP.not_dvd_of_degree_lt (C_ne_zero.2 hx0) ?_ hx
    rw [degree_C hx0, degree_X_pow_sub_C (Nat.pos_of_ne_zero hp0)]
    exact_mod_cast Nat.pos_of_ne_zero hp0
  have hev : P.eval₂ (π : A →+* Ω) 1 = 0 := by
    simp [P, eval₂_sub, ha]
  let g : AdjoinRoot P →+* Ω := AdjoinRoot.lift (π : A →+* Ω) 1 hev
  have hg : ∀ x, g (f x) = π x := fun x => by
    rw [hf]; exact AdjoinRoot.lift_of hev
  have hgr : g (AdjoinRoot.root P) = 1 := AdjoinRoot.lift_root hev
  let π' : AdjoinRoot P →ₐ[Ω] Ω :=
    { g with
      commutes' := fun c => by
        have : algebraMap Ω (AdjoinRoot P) c = f (algebraMap Ω A c) := (f.commutes c).symm
        change g _ = _
        rw [this, hg, π.commutes] }
  have hroot : AdjoinRoot.root P ^ p = f a.val := by
    have h := AdjoinRoot.eval₂_root P
    simp only [P, eval₂_sub, eval₂_X_pow, eval₂_C] at h
    exact sub_eq_zero.1 h
  have hu : IsUnit (AdjoinRoot.root P) := by
    rw [← isUnit_pow_iff hp0, hroot]
    exact a.isUnit.map f
  haveI : Nontrivial (AdjoinRoot P) := g.domain_nontrivial
  haveI : CharP (AdjoinRoot P) p :=
    charP_of_injective_algebraMap (algebraMap Ω (AdjoinRoot P)).injective p
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, f, π', hu.unit, hinj, ?_, ?_, hgr, ?_⟩
  · ext x; exact hg x
  · set I : Ideal (AdjoinRoot P) := (RingHom.ker π).map f with hI
    have hIn : IsNilpotent I := by
      obtain ⟨n, hn⟩ := hπ
      refine ⟨n, ?_⟩
      rw [hI, ← Ideal.map_pow, hn]
      exact Ideal.map_bot
    set J : Ideal (AdjoinRoot P) := Ideal.span {AdjoinRoot.root P - 1} with hJ
    have hJn : IsNilpotent J := by
      obtain ⟨n, hn⟩ := hIn
      refine ⟨p * n, ?_⟩
      rw [pow_mul, Ideal.zero_eq_bot, eq_bot_iff, ← Ideal.zero_eq_bot, ← hn]
      apply Ideal.pow_right_mono
      rw [hJ, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, sub_pow_char, hroot,
        one_pow, ← map_one f, ← map_sub]
      apply Ideal.mem_map_of_mem
      rw [RingHom.mem_ker, map_sub, ha, map_one, sub_self]
    obtain ⟨n, hn⟩ := (Commute.all I J).isNilpotent_add hIn hJn
    refine ⟨n, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← Ideal.zero_eq_bot, ← hn]
    apply Ideal.pow_right_mono
    intro x hx
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
    obtain ⟨r, hr⟩ : (X - C 1 : A[X]) ∣ q - C (q.eval 1) := X_sub_C_dvd_sub_C_eval
    have h1 : AdjoinRoot.mk P q = f (q.eval 1) + (AdjoinRoot.root P - 1) * AdjoinRoot.mk P r := by
      have := congrArg (AdjoinRoot.mk P) hr
      simp only [map_sub, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_one] at this
      rw [hf, ← this]; ring
    have hx' : g (AdjoinRoot.mk P q) = 0 := hx
    rw [h1, map_add, map_mul, map_sub, hgr, map_one, sub_self, zero_mul, add_zero, hg] at hx'
    rw [h1, Ideal.add_eq_sup]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hx')
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  · ext
    simpa using hroot

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `A _ _ π hπ a _`. Conclude with `⟨A, inferInstance, inferInstance, AlgHom.id Ω A, π, a, Function.injective_id, rfl, hπ, fun i => i.elim0, fun i => i.elim0⟩`. Consider the case `succ n ih`.

Introduce `A _ _ π hπ a ha`. Take `⟨B, _, _, f, ρ, s, hf, hρ, hρn, hs1, hs⟩` from `ih A π hπ (fun i => a i.succ) (fun i => ha i.succ)`. Establish `h0 : ρ (Units.map (f : A →* B) (a 0)).val = 1`. Use `congrArg (fun φ : A →ₐ[Ω] Ω => φ (a 0).val) hρ` as an intermediate fact. Simplify `this` using `[ha 0]`.

Take `⟨C, _, _, g, σ, t, hg, hσ, hσn, ht1, ht⟩` from `exists_root_one Ω p B ρ hρn _ h0`. Use `⟨C, inferInstance, inferInstance, g.comp f, σ, Fin.cons t (fun i => Units.map (g : B →* C) (s i)), hg.comp hf, ?_, hσn, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← AlgHom.comp_assoc, hσ, hρ]`. Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations.

Simplify using `using ht1`. Use `congrArg (fun φ : B →ₐ[Ω] Ω => φ (s j).val) hσ` as an intermediate fact. Simplify `this` using `[hs1 j]`. Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations.

Rewrite using `[Fin.cons_zero, ht]`. Both sides reduce to the same expression. Rewrite using `[Fin.cons_succ, ← map_pow, hs j]`. Both sides reduce to the same expression.
-/
theorem exists_root_fin (Ω : Type) [Field Ω] (p : ℕ) [hp : Fact p.Prime] [CharP Ω p] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω) (_ : IsNilpotent (RingHom.ker π))
    (a : Fin n → Aˣ) (_ : ∀ i, π (a i).val = 1),
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω)
      (s : Fin n → A'ˣ), Function.Injective f ∧ π'.comp f = π ∧ IsNilpotent (RingHom.ker π') ∧
      (∀ i, π' (s i).val = 1) ∧ ∀ i, s i ^ p = Units.map (f : A →* A') (a i) := by
  induction n with
  | zero =>
    intro A _ _ π hπ a _
    exact ⟨A, inferInstance, inferInstance, AlgHom.id Ω A, π, a, Function.injective_id, rfl, hπ,
      fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro A _ _ π hπ a ha
    obtain ⟨B, _, _, f, ρ, s, hf, hρ, hρn, hs1, hs⟩ :=
      ih A π hπ (fun i => a i.succ) (fun i => ha i.succ)
    have h0 : ρ (Units.map (f : A →* B) (a 0)).val = 1 := by
      have := congrArg (fun φ : A →ₐ[Ω] Ω => φ (a 0).val) hρ
      simpa [ha 0] using this
    obtain ⟨C, _, _, g, σ, t, hg, hσ, hσn, ht1, ht⟩ :=
      exists_root_one Ω p B ρ hρn _ h0
    refine ⟨C, inferInstance, inferInstance, g.comp f, σ,
      Fin.cons t (fun i => Units.map (g : B →* C) (s i)), hg.comp hf, ?_, hσn, ?_, ?_⟩
    · rw [← AlgHom.comp_assoc, hσ, hρ]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ht1
      · have := congrArg (fun φ : B →ₐ[Ω] Ω => φ (s j).val) hσ
        simpa [hs1 j] using this
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero, ht]; rfl
      · rw [Fin.cons_succ, ← map_pow, hs j]; rfl

/- English proof (translation)
Introduce `Ω _ p _ _ X _ _ _ A _ _ π hπ χ hχ`. Set `b` to `Module.finBasis ℤ X`. Take `⟨B, _, _, f, ρ, s, hf, hρ, hρn, hs1, hs⟩` from `exists_root_fin Ω p _ A π hπ (fun i => χ (Multiplicative.ofAdd (b i))) (fun i => hχ _)`. Set `l : X →ₗ[ℤ] Additive Bˣ` to `b.constr ℤ (fun i => Additive.ofMul (s i))`. Establish `hl : ∀ i, l (b i) = Additive.ofMul (s i)` using `fun i => b.constr_basis ℤ _ i`.

Set `χ' : Multiplicative X →* Bˣ` to `AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom`. Establish `hχ' : ∀ i, χ' (Multiplicative.ofAdd (b i)) = s i` using `fun i => by`. Express the relevant statement in the definitionally equal form `Additive.toMul (l (b i)) = _`. Rewrite using `[hl]`. Both sides reduce to the same expression.

Establish `key : ∀ {G : Type} [CommGroup G] (φ ψ : Multiplicative X →* G), (∀ i, φ (Multiplicative.ofAdd (b i)) = ψ (Multiplicative.ofAdd (b i))) → φ = ψ`. Introduce `G _ φ ψ h`. Establish `: (MonoidHom.toAdditiveRight φ).toIntLinearMap = (MonoidHom.toAdditiveRight ψ).toIntLinearMap` using `b.ext fun i => congrArg Additive.ofMul (h i)`. Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations. Conclude with `congrArg Additive.toMul (LinearMap.congr_fun this x.toAdd)`.

Use `⟨B, inferInstance, inferInstance, f, ρ, χ', hf, hρ, hρn, ?_, ?_⟩` and prove the remaining obligations. Establish `: (Units.map (ρ : B →* Ω)).comp χ' = 1` using `key _ _ fun i => by`. Use `ext`. Simplify `hs1 i` using `[hχ']`. Introduce `x`.

Conclude with `congrArg Units.val (DFunLike.congr_fun this x)`. Conclude with `key _ _ fun i => by`. Rewrite using `[MonoidHom.pow_apply, hχ', hs]`. Both sides reduce to the same expression.
-/
theorem exists_root_character :
    ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (A : Type) [CommRing A] [Algebra Ω A]
    (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ χ : Multiplicative X →* Aˣ,
    (∀ x, π (χ x).val = 1) →
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra Ω A') (f : A →ₐ[Ω] A') (π' : A' →ₐ[Ω] Ω)
      (χ' : Multiplicative X →* A'ˣ), Function.Injective f ∧ π'.comp f = π ∧
      IsNilpotent (RingHom.ker π') ∧ (∀ x, π' (χ' x).val = 1) ∧
      χ' ^ p = (Units.map (f : A →* A')).comp χ := by
  intro Ω _ p _ _ X _ _ _ A _ _ π hπ χ hχ
  let b := Module.finBasis ℤ X
  obtain ⟨B, _, _, f, ρ, s, hf, hρ, hρn, hs1, hs⟩ :=
    exists_root_fin Ω p _ A π hπ (fun i => χ (Multiplicative.ofAdd (b i))) (fun i => hχ _)
  let l : X →ₗ[ℤ] Additive Bˣ := b.constr ℤ (fun i => Additive.ofMul (s i))
  have hl : ∀ i, l (b i) = Additive.ofMul (s i) := fun i => b.constr_basis ℤ _ i
  let χ' : Multiplicative X →* Bˣ := AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom
  have hχ' : ∀ i, χ' (Multiplicative.ofAdd (b i)) = s i := fun i => by
    change Additive.toMul (l (b i)) = _
    rw [hl]; rfl
  have key : ∀ {G : Type} [CommGroup G] (φ ψ : Multiplicative X →* G),
      (∀ i, φ (Multiplicative.ofAdd (b i)) = ψ (Multiplicative.ofAdd (b i))) → φ = ψ := by
    intro G _ φ ψ h
    have : (MonoidHom.toAdditiveRight φ).toIntLinearMap =
        (MonoidHom.toAdditiveRight ψ).toIntLinearMap :=
      b.ext fun i => congrArg Additive.ofMul (h i)
    refine MonoidHom.ext fun x => ?_
    exact congrArg Additive.toMul (LinearMap.congr_fun this x.toAdd)
  refine ⟨B, inferInstance, inferInstance, f, ρ, χ', hf, hρ, hρn, ?_, ?_⟩
  · have : (Units.map (ρ : B →* Ω)).comp χ' = 1 := key _ _ fun i => by
      ext
      simpa [hχ'] using hs1 i
    intro x
    exact congrArg Units.val (DFunLike.congr_fun this x)
  · exact key _ _ fun i => by
      rw [MonoidHom.pow_apply, hχ', hs]; rfl

end GlobalTheory.TorusRoot
